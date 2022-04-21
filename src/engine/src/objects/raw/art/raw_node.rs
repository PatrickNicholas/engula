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

use std::marker::PhantomData;

use super::{ArtLeaf, BoxNode, Node};
use crate::elements::{BoxElement, Element, ElementLayout};

const NODE_EMPTY: u8 = 0;
const NODE_4: u8 = 1;
const NODE_16: u8 = 2;
const NODE_48: u8 = 3;
const NODE_256: u8 = 4;
const NODE_LEAF: u8 = 5;

const fn node_tag(value: usize) -> u8 {
    match value {
        4 => NODE_4,
        16 => NODE_16,
        48 => NODE_48,
        256 => NODE_256,
        _ => panic!("unknown node type"),
    }
}

pub enum NodeType<'a, L: ArtLeaf> {
    Empty,
    Node4(&'a Element<Node<4, L>>),
    Node16(&'a Element<Node<16, L>>),
    Node48(&'a Element<Node<48, L>>),
    Node256(&'a Element<Node<256, L>>),
    Leaf(&'a Element<L>),
}

pub enum NodeTypeMut<'a, L: ArtLeaf> {
    Empty,
    Node4(&'a mut Element<Node<4, L>>),
    Node16(&'a mut Element<Node<16, L>>),
    Node48(&'a mut Element<Node<48, L>>),
    Node256(&'a mut Element<Node<256, L>>),
    Leaf(&'a mut Element<L>),
}

#[repr(C)]
pub struct RawNode<L: ArtLeaf> {
    values: [u8; 8],
    _mark: PhantomData<*mut Element<L>>,
}

impl<L: ArtLeaf> RawNode<L> {
    pub fn from_leaf(leaf: BoxElement<L>) -> Self {
        let address = BoxElement::leak(leaf).as_ptr() as *const _ as usize;
        let mut values = address.to_le_bytes();
        values[7] = NODE_LEAF;
        RawNode {
            values,
            _mark: Default::default(),
        }
    }

    pub fn from_node<const N: usize>(node: BoxNode<N, L>) -> Self {
        let address = BoxNode::leak(node).as_ptr() as *const _ as usize;
        let mut values = address.to_le_bytes();
        values[7] = node_tag(N);
        RawNode {
            values,
            _mark: Default::default(),
        }
    }

    pub fn from_node_ref<const N: usize>(node: &Element<Node<N, L>>) -> Self {
        let address = node as *const _ as usize;
        let mut values = address.to_le_bytes();
        values[7] = node_tag(N);
        RawNode {
            values,
            _mark: Default::default(),
        }
    }

    pub fn from_leaf_ref(leaf: &Element<L>) -> Self {
        let address = leaf as *const _ as usize;
        let mut values = address.to_le_bytes();
        values[7] = NODE_LEAF;
        RawNode {
            values,
            _mark: Default::default(),
        }
    }
}

impl<L: ArtLeaf> RawNode<L> {
    #[inline(always)]
    pub fn as_mut<'a>(&self) -> NodeTypeMut<'a, L> {
        unsafe {
            match self.values[7] {
                NODE_EMPTY => NodeTypeMut::Empty,
                NODE_4 => NodeTypeMut::Node4(self.cast_mut()),
                NODE_16 => NodeTypeMut::Node16(self.cast_mut()),
                NODE_48 => NodeTypeMut::Node48(self.cast_mut()),
                NODE_256 => NodeTypeMut::Node256(self.cast_mut()),
                NODE_LEAF => NodeTypeMut::Leaf(self.cast_mut()),
                v => panic!("unknown node type {}", v),
            }
        }
    }

    #[inline(always)]
    pub fn as_ref<'a>(&self) -> NodeType<'a, L> {
        unsafe {
            match self.values[7] {
                NODE_EMPTY => NodeType::Empty,
                NODE_4 => NodeType::Node4(self.cast()),
                NODE_16 => NodeType::Node16(self.cast()),
                NODE_48 => NodeType::Node48(self.cast()),
                NODE_256 => NodeType::Node256(self.cast()),
                NODE_LEAF => NodeType::Leaf(self.cast()),
                v => panic!("unknown node type {}", v),
            }
        }
    }

    pub fn is_empty_node(&self) -> bool {
        self.values[7] == NODE_EMPTY
    }

    unsafe fn address(&self) -> usize {
        let mut values = self.values;
        values[6] = 0;
        values[7] = 0;
        std::mem::transmute_copy(&values)
    }

    unsafe fn cast<'a, T>(&self) -> &'a Element<T>
    where
        T: ElementLayout,
    {
        &*(self.address() as *const Element<T>)
    }

    unsafe fn cast_mut<'a, T>(&self) -> &'a mut Element<T>
    where
        T: ElementLayout,
    {
        &mut *(self.address() as *mut Element<T>)
    }
}

impl<L: ArtLeaf> Default for RawNode<L> {
    fn default() -> Self {
        RawNode {
            values: [0; 8],
            _mark: Default::default(),
        }
    }
}

impl<L: ArtLeaf> Clone for RawNode<L> {
    fn clone(&self) -> Self {
        RawNode {
            values: self.values,
            _mark: Default::default(),
        }
    }
}

impl<L: ArtLeaf> Copy for RawNode<L> {}

#[allow(dead_code)]
fn assert_raw_node_size() {
    struct Bar {
        foo: usize,
    }
    impl ElementLayout for Bar {
        fn element_type() -> u16 {
            0
        }
        fn layout(_: &Element<Self>) -> std::alloc::Layout {
            std::alloc::Layout::new::<Element<Self>>()
        }
    }
    impl ArtLeaf for Bar {
        fn art_key<'a>(&self) -> &'a [u8] {
            &[]
        }
    }

    let _: [u8; std::mem::size_of::<usize>()] = [0; std::mem::size_of::<RawNode<Bar>>()];
}
