// Copyright 2022 The Engula Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::{
    alloc::{alloc, Layout},
    ptr::NonNull,
};

use super::{ArtLeaf, RawNode};
use crate::{
    elements::ElementType,
    objects::{BoxElement, Element, ElementLayout},
};

pub const MAX_CACHED_PREFIX: usize = 8;

#[repr(C)]
pub struct Node<const N: usize, L: ArtLeaf> {
    pub leaf: RawNode<L>,
    children: [RawNode<L>; N],
    pub cached_prefix: [u8; MAX_CACHED_PREFIX],
    compressed_prefix_len: u32,
    num_children: u32,
    keys: [u8; N],
}

impl<const N: usize, L: ArtLeaf> Node<N, L> {
    pub fn compressed_prefix_len(&self) -> usize {
        self.compressed_prefix_len as usize
    }

    pub fn first_child(&self) -> RawNode<L> {
        if !self.leaf.is_empty_node() {
            self.leaf
        } else {
            assert!(self.num_children >= 1);
            self.children[0]
        }
    }

    pub fn install_prefix(&mut self, prefix: &[u8]) {
        let limit = std::cmp::min(prefix.len(), MAX_CACHED_PREFIX);
        self.cached_prefix[..limit].copy_from_slice(&prefix[..limit]);
        self.compressed_prefix_len = prefix.len() as u32;
    }

    pub fn add_child(&mut self, byte: u8, value: BoxElement<L>) {
        self.add_child_node(byte, RawNode::from_leaf(value));
    }

    pub fn add_child_node(&mut self, byte: u8, node: RawNode<L>) {
        let num_children = self.num_children as usize;
        debug_assert!(num_children < MAX_CACHED_PREFIX);

        let idx = self.get_sorted_index(byte);
        if idx < num_children {
            self.keys[..].copy_within(idx..num_children, idx + 1);
            self.children[..].copy_within(idx..num_children, idx + 1);
        }

        self.keys[idx] = byte;
        self.children[idx] = node;
        self.num_children += 1;
        println!(
            "add_child_node: idx {} byte {}, num_children {}, keys {:?}",
            idx, byte, self.num_children, self.keys
        );
    }

    pub fn find_child_mut(&mut self, byte: u8) -> Option<&mut RawNode<L>> {
        let num_children = self.num_children as usize;
        assert!(num_children < self.keys.len());

        for i in 0..num_children {
            if self.keys[i] == byte {
                return Some(&mut self.children[i]);
            }
        }
        println!(
            "find_child_mut: num_children {}, keys {:?}",
            self.num_children, self.keys
        );
        None
    }

    pub fn find_child(&self, byte: u8) -> Option<RawNode<L>> {
        let num_children = self.num_children as usize;
        assert!(num_children < self.keys.len());

        for i in 0..num_children {
            if self.keys[i] == byte {
                return Some(self.children[i]);
            }
        }
        None
    }

    fn get_sorted_index(&self, byte: u8) -> usize {
        let mut i: usize = 0;
        while i < self.num_children as usize && byte > self.keys[i] {
            i += 1;
        }
        i
    }

    fn is_full(&self) -> bool {
        self.num_children as usize == N
    }

    pub fn remove_child(&mut self, byte: u8) {
        let num_children = self.num_children as usize;
        let idx = self.get_sorted_index(byte);
        println!(
            "remove_child, byte {}, idx {}, num_children {}",
            byte, idx, num_children
        );
        if idx < num_children {
            self.keys[..].copy_within(idx + 1..num_children, idx);
            self.children[..].copy_within(idx + 1..num_children, idx);
            self.num_children -= 1;
        }
    }
}

impl<const N: usize, L: ArtLeaf> BoxElement<Node<N, L>> {
    pub fn new() -> Self {
        unsafe {
            let layout = Layout::new::<Element<Node<N, L>>>();
            let mut ptr = NonNull::new_unchecked(alloc(layout)).cast::<Element<Node<N, L>>>();
            let uninit_node = ptr.as_uninit_mut();
            uninit_node.write(Element::new(Node::<N, L>::default()));
            BoxElement::from_raw(ptr)
        }
    }
}

impl<const N: usize, L: ArtLeaf> Element<Node<N, L>> {
    pub fn add_record<const NN: usize>(&mut self, byte: u8, value: BoxElement<L>) -> RawNode<L> {
        if self.is_full() {
            self.grow_and_add::<NN>(byte, value)
        } else {
            self.add_child(byte, value);
            RawNode::from_node_ref(self)
        }
    }

    fn grow_and_add<const NN: usize>(&mut self, byte: u8, value: BoxElement<L>) -> RawNode<L> {
        let mut new_node = BoxNode::<NN, L>::new();
        new_node.num_children = self.num_children;
        new_node.compressed_prefix_len = self.compressed_prefix_len;
        for i in 0..self.num_children as usize {
            new_node.keys[i] = self.keys[i];
            new_node.children[i] = std::mem::take(&mut self.children[i]);
        }
        new_node.add_child(byte, value);

        self.num_children = 0;
        self.compressed_prefix_len = 0;

        unsafe {
            BoxElement::from_raw(NonNull::from(self));
        }

        RawNode::from_node(new_node)
    }
}

pub type BoxNode<const N: usize, L> = BoxElement<Node<N, L>>;

impl<const N: usize, L: ArtLeaf> Drop for Node<N, L> {
    fn drop(&mut self) {
        assert!(self.leaf.is_empty_node());
        assert_eq!(self.num_children, 0);
    }
}

impl<const N: usize, L: ArtLeaf> Default for Node<N, L> {
    fn default() -> Self {
        Node {
            leaf: RawNode::default(),
            num_children: 0,
            compressed_prefix_len: 0,
            cached_prefix: [0; 8],
            keys: [0; N],
            children: [RawNode::default(); N],
        }
    }
}

impl<const N: usize, L: ArtLeaf> ElementLayout for Node<N, L> {
    fn element_type() -> u16 {
        ElementType::ART_NODE.bits()
    }

    fn layout(_: &Element<Self>) -> Layout {
        Layout::new::<Element<Self>>()
    }
}
