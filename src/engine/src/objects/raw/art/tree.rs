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

use std::{marker::PhantomData, ptr::NonNull};

use super::{ArtLeaf, BoxNode, Node, NodeType, NodeTypeMut, RawNode, MAX_CACHED_PREFIX};
use crate::objects::{BoxElement, Element};

fn match_keys(lhs: &[u8], rhs: &[u8]) -> usize {
    lhs.iter()
        .zip(rhs.iter())
        .take_while(|(a, b)| a == b)
        .count()
}

#[repr(C)]
pub struct Art<L: ArtLeaf> {
    root: RawNode<L>,
    size: usize,
    _data: PhantomData<L>,
}

impl<L: ArtLeaf> Art<L> {
    pub fn new() -> Self {
        Art {
            root: Default::default(),
            size: 0,
            _data: Default::default(),
        }
    }

    pub fn get(&self, key: &[u8]) -> Option<&Element<L>> {
        self.search_record(self.root, 0, key)
    }

    /// To insert new data, the user must ensure that no same key exists, otherwise the existing key
    /// will be discarded directly.
    pub fn insert_without_conflicts(&mut self, value: BoxElement<L>) {
        let key = value.art_key();
        assert!(!key.is_empty());
        self.root = self.insert_record(self.root, 0, key, value);
    }

    pub fn remove_entry(&mut self, key: &[u8]) -> Option<BoxElement<L>> {
        let (new_root, retval) = self.remove_record(self.root, 0, key);
        self.root = new_root;
        retval
    }

    pub fn len(&self) -> usize {
        self.size
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }
}

impl<L: ArtLeaf> Art<L> {
    fn insert_record(
        &mut self,
        raw_node: RawNode<L>,
        depth: usize,
        key: &[u8],
        value: BoxElement<L>,
    ) -> RawNode<L> {
        match raw_node.as_mut() {
            NodeTypeMut::Empty => {
                self.size += 1;
                RawNode::from_leaf(value)
            }
            NodeTypeMut::Node4(node) => self.node_insert::<4, 16>(node, depth, key, value),
            NodeTypeMut::Node16(node) => self.node_insert::<16, 48>(node, depth, key, value),
            NodeTypeMut::Node48(node) => self.node_insert::<48, 256>(node, depth, key, value),
            NodeTypeMut::Node256(node) => self.node_insert::<256, 256>(node, depth, key, value),
            NodeTypeMut::Leaf(leaf) => self.leaf_insert(leaf, depth, key, value),
        }
    }

    fn node_insert<const N: usize, const NN: usize>(
        &mut self,
        node: &mut Element<Node<N, L>>,
        depth: usize,
        key: &[u8],
        value: BoxElement<L>,
    ) -> RawNode<L> {
        let num_compressed = node.compressed_prefix_len();
        let num_cached = std::cmp::min(MAX_CACHED_PREFIX, num_compressed);
        let num_matched = match_keys(&node.cached_prefix[..num_cached], &key[depth..]);
        if num_matched == MAX_CACHED_PREFIX {
            // All cached prefix are matched, load entire key and retry.
            let compressed_prefix = self.load_compressed_prefix(node, depth);
            let num_matched = match_keys(compressed_prefix, &key[depth..]);
            if num_matched < num_compressed {
                return self.expand_path(node, compressed_prefix, num_matched, depth, key, value);
            }
        } else if num_matched < num_cached {
            // expand cached path, save cached prefix in stack.
            let cached_prefix = node.cached_prefix;
            return self.expand_path(
                node,
                &cached_prefix[..num_cached],
                num_matched,
                depth,
                key,
                value,
            );
        }

        let depth = depth + num_compressed;
        if depth == key.len() {
            node.leaf = RawNode::from_leaf(value);
            return RawNode::from_node_ref(node);
        }

        let next_byte = key[depth];
        match node.find_child_mut(next_byte) {
            Some(child) => {
                *child = self.insert_record(*child, depth + 1, key, value);
                RawNode::from_node_ref(node)
            }
            None => node.add_record::<NN>(next_byte, value),
        }
    }

    fn node_add_child<const N: usize>(
        new_node: &mut Node<N, L>,
        depth: usize,
        key: &[u8],
        raw_node: RawNode<L>,
    ) {
        if key.len() == depth {
            new_node.leaf = raw_node;
        } else {
            new_node.add_child_node(key[depth], raw_node);
        }
    }

    fn leaf_insert(
        &mut self,
        leaf: &mut Element<L>,
        depth: usize,
        key: &[u8],
        value: BoxElement<L>,
    ) -> RawNode<L> {
        let leaf_key = leaf.art_key();
        debug_assert!(depth <= key.len());
        debug_assert!(
            depth <= leaf_key.len(),
            "key {:?}, leaf key {:?} depth {}",
            key,
            leaf_key,
            depth
        );

        let num_matched = match_keys(&leaf_key[depth..], &key[depth..]);
        if num_matched == leaf_key.len() && num_matched == key.len() {
            return RawNode::from_leaf(value);
        }

        // Avoid situations where one key is a prefix of another.
        // let mut limit = depth + num_matched;
        // if num_matched > 0 && (limit == leaf_key.len() || limit == key.len()) {
        //     assert!(limit > 0);
        //     limit -= 1;
        // }

        let limit = depth + num_matched;
        let mut new_node = BoxNode::<4, L>::new();
        new_node.install_prefix(&key[depth..limit]);
        Self::node_add_child(&mut new_node, limit, key, RawNode::from_leaf(value));
        Self::node_add_child(&mut new_node, limit, leaf_key, RawNode::from_leaf_ref(leaf));

        // println!(
        //     "leaf node insert, num matched {}, leaf key byte {}, key byte {}",
        //     num_matched, leaf_key[limit], key[limit]
        // );
        self.size += 1;

        RawNode::from_node(new_node)
    }

    fn expand_path<const N: usize>(
        &mut self,
        node: &mut Element<Node<N, L>>,
        compressed_prefix: &[u8],
        num_matched: usize,
        depth: usize,
        key: &[u8],
        value: BoxElement<L>,
    ) -> RawNode<L> {
        debug_assert!(num_matched < compressed_prefix.len());

        let mut new_node = BoxNode::<4, L>::new();
        new_node.install_prefix(&compressed_prefix[..num_matched]);
        Self::node_add_child(
            &mut new_node,
            depth + num_matched,
            key,
            RawNode::from_leaf(value),
        );
        // new_node.add_child(key[depth + num_matched], value);

        // shrink the original node's compressed path.
        let compressed_next_byte = compressed_prefix[num_matched];
        node.install_prefix(&compressed_prefix[num_matched + 1..]);
        new_node.add_child_node(compressed_next_byte, RawNode::from_node_ref(node));

        RawNode::from_node(new_node)
    }

    fn find_minimum<'a>(&self, mut raw_node: RawNode<L>) -> &'a L {
        loop {
            raw_node = match raw_node.as_ref() {
                NodeType::Empty => {
                    panic!("find_minimum reach a empty node");
                }
                NodeType::Node4(node) => node.first_child(),
                NodeType::Node16(node) => node.first_child(),
                NodeType::Node48(node) => node.first_child(),
                NodeType::Node256(node) => node.first_child(),
                NodeType::Leaf(leaf) => return leaf,
            }
        }
    }

    fn load_compressed_prefix<'a, const N: usize>(
        &self,
        node: &Element<Node<N, L>>,
        depth: usize,
    ) -> &'a [u8] {
        let leaf = self.find_minimum(node.first_child());
        let key = &leaf.art_key()[depth..];
        let limit = node.compressed_prefix_len();
        &key[..limit]
    }
}

// For search
impl<L: ArtLeaf> Art<L> {
    fn remove_record(
        &mut self,
        raw_node: RawNode<L>,
        depth: usize,
        key: &[u8],
    ) -> (RawNode<L>, Option<BoxElement<L>>) {
        match raw_node.as_mut() {
            NodeTypeMut::Empty => {
                panic!("remove_record reach empty node");
            }
            NodeTypeMut::Node4(node) => self.node_remove::<4>(node, depth, key),
            NodeTypeMut::Node16(node) => self.node_remove::<16>(node, depth, key),
            NodeTypeMut::Node48(node) => self.node_remove::<48>(node, depth, key),
            NodeTypeMut::Node256(node) => self.node_remove::<256>(node, depth, key),
            NodeTypeMut::Leaf(leaf) => self.leaf_remove(leaf, key),
        }
    }

    fn node_remove<const N: usize>(
        &mut self,
        node: &mut Element<Node<N, L>>,
        depth: usize,
        key: &[u8],
    ) -> (RawNode<L>, Option<BoxElement<L>>) {
        // Because `leaf_remove` will check whether the key matches, so here we do not check the
        // compressed prefix.
        let depth = depth + node.compressed_prefix_len();
        if depth > key.len() {
            println!(
                "node_remove: skip because depth {} is large than key len {}",
                depth,
                key.len()
            );
            return (RawNode::from_node_ref(node), None);
        }

        if depth == key.len() {
            let (_, retval) = match std::mem::take(&mut node.leaf).as_mut() {
                NodeTypeMut::Leaf(leaf) => self.leaf_remove(leaf, key),
                NodeTypeMut::Empty => (RawNode::default(), None),
                _ => panic!("node leaf isn't leaf type"),
            };
            return (RawNode::from_node_ref(node), retval);
        }

        let next_byte = key[depth];
        let child = match node.find_child_mut(next_byte) {
            Some(child) => child,
            None => {
                println!("node_remove: no such child exists {}", next_byte);
                return (RawNode::from_node_ref(node), None);
            }
        };

        let (raw_node, retval) = self.remove_record(*child, depth + 1, key);
        *child = raw_node;
        if retval.is_some() {
            node.remove_child(next_byte);
        }
        (RawNode::from_node_ref(node), retval)
    }

    fn leaf_remove(
        &mut self,
        leaf: &mut Element<L>,
        key: &[u8],
    ) -> (RawNode<L>, Option<BoxElement<L>>) {
        println!("leaf_remove: leaf key {:?}, arg {:?}", leaf.art_key(), key);
        if leaf.art_key() != key {
            (RawNode::from_leaf_ref(leaf), None)
        } else {
            self.size -= 1;

            unsafe {
                // Safety: Once leaf is hosted on box, the reference to it will be set to
                // `RawNode::default`.
                let boxed_leaf = BoxElement::from_raw(NonNull::from(leaf));
                (RawNode::default(), Some(boxed_leaf))
            }
        }
    }
}

// For delete
impl<L: ArtLeaf> Art<L> {
    fn search_record<'a>(
        &self,
        raw_node: RawNode<L>,
        depth: usize,
        key: &[u8],
    ) -> Option<&'a Element<L>> {
        match raw_node.as_ref() {
            NodeType::Node4(node) => self.node_search::<4>(node, depth, key),
            NodeType::Node16(node) => self.node_search::<16>(node, depth, key),
            NodeType::Node48(node) => self.node_search::<48>(node, depth, key),
            NodeType::Node256(node) => self.node_search::<256>(node, depth, key),
            NodeType::Leaf(leaf) => self.leaf_search(leaf, key),
            NodeType::Empty => {
                panic!("reach a empty node");
            }
        }
    }

    fn node_search<'a, const N: usize>(
        &self,
        node: &Element<Node<N, L>>,
        depth: usize,
        key: &[u8],
    ) -> Option<&'a Element<L>> {
        let depth = depth + node.compressed_prefix_len();
        if depth > key.len() {
            return None;
        }
        if depth == key.len() {
            return match node.leaf.as_ref() {
                NodeType::Leaf(leaf) => self.leaf_search(leaf, key),
                NodeType::Empty => None,
                _ => panic!("node leaf isn't leaf type"),
            };
        }

        let next_byte = key[depth];
        match node.find_child(next_byte) {
            Some(child) => self.search_record(child, depth + 1, key),
            None => None,
        }
    }

    fn leaf_search<'a>(&self, leaf: &'a Element<L>, key: &[u8]) -> Option<&'a Element<L>> {
        if leaf.art_key() == key {
            Some(leaf)
        } else {
            None
        }
    }
}

impl<N: ArtLeaf> Default for Art<N> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elements::array::Array;

    impl ArtLeaf for Array {
        fn art_key<'a>(&self) -> &'a [u8] {
            unsafe { &*(self.data_slice() as *const [u8]) }
        }
    }

    #[test]
    fn art_basic() {
        let mut art = Art::<Array>::new();
        assert_eq!(art.len(), 0);
        assert!(art.is_empty());

        let expect_key = vec![0u8, 1, 2, 3, 4, 5, 6, 7, 8, 9];

        let mut array = BoxElement::<Array>::with_capacity(10);
        array.data_slice_mut().copy_from_slice(&expect_key);
        art.insert_without_conflicts(array);

        assert_eq!(art.len(), 1);
        assert!(!art.is_empty());

        let value = art.get(&expect_key);
        assert!(value.is_some());
        let value = value.unwrap();
        assert_eq!(value.data_slice(), expect_key);

        art.remove_entry(&expect_key);

        assert_eq!(art.len(), 0);
        assert!(art.is_empty());
    }

    #[test]
    fn lazy_expansion() {
        let expect_key = "foo".as_bytes();
        let mut art = Art::<Array>::new();

        let mut array = BoxElement::<Array>::with_capacity(expect_key.len());
        array.data_slice_mut().copy_from_slice(&expect_key);
        unsafe {
            let raw_node = art.insert_record(RawNode::default(), 0, expect_key, array);
            let leaf = match raw_node.as_ref() {
                NodeType::Leaf(leaf) => leaf,
                _ => panic!("wrong node type"),
            };
            BoxElement::from_raw(NonNull::from(leaf));
        }
    }

    #[test]
    fn path_compression() {
        struct TestCase {
            expect_key_1: Vec<u8>,
            expect_key_2: Vec<u8>,
            expect_prefix_len: usize,
            cached_prefix: Vec<u8>,
        }

        let cases = vec![
            // 1. normal case
            TestCase {
                expect_key_1: "bar".as_bytes().to_vec(),
                expect_key_2: "baz".as_bytes().to_vec(),
                expect_prefix_len: 2,
                cached_prefix: "ba".as_bytes().to_vec(),
            },
            // 2. exceeds cache prefix buffer.
            TestCase {
                expect_key_1: "ba123456789r".as_bytes().to_vec(),
                expect_key_2: "ba123456789z".as_bytes().to_vec(),
                expect_prefix_len: 11,
                cached_prefix: "ba123456".as_bytes().to_vec(),
            },
        ];

        for TestCase {
            expect_key_1,
            expect_key_2,
            expect_prefix_len,
            cached_prefix,
        } in cases
        {
            let mut art = Art::<Array>::new();

            let mut value_1 = BoxElement::<Array>::with_capacity(expect_key_1.len());
            value_1.data_slice_mut().copy_from_slice(&expect_key_1);
            let mut value_2 = BoxElement::<Array>::with_capacity(expect_key_2.len());
            value_2.data_slice_mut().copy_from_slice(&expect_key_2);
            let value_1_node = art.insert_record(RawNode::default(), 0, &expect_key_1, value_1);
            assert!(matches!(value_1_node.as_ref(), NodeType::Leaf(_)));
            let value_2_node = art.insert_record(value_1_node, 0, &expect_key_2, value_2);
            assert!(matches!(value_2_node.as_ref(), NodeType::Node4(_)));
            unsafe {
                let node = match value_2_node.as_mut() {
                    NodeTypeMut::Node4(node) => node,
                    _ => panic!("wrong node type"),
                };
                assert_eq!(node.compressed_prefix_len(), expect_prefix_len);
                assert_eq!(
                    &node.cached_prefix
                        [..std::cmp::min(node.compressed_prefix_len(), MAX_CACHED_PREFIX)],
                    &cached_prefix
                );
                drop(node);
                art.remove_record(value_2_node, 0, &expect_key_1);
                art.remove_record(value_2_node, 0, &expect_key_2);

                let node = match value_2_node.as_mut() {
                    NodeTypeMut::Node4(node) => node,
                    _ => panic!("wrong node type"),
                };
                BoxElement::from_raw(NonNull::from(node));
            }
        }
    }

    #[test]
    fn insert_suffix() {
        let mut art = Art::<Array>::new();
        let keys: Vec<Vec<u8>> = vec![
            "foo".as_bytes().into(),
            "foo1".as_bytes().into(),
            "foo12".as_bytes().into(),
            "foo123".as_bytes().into(),
        ];

        let mut root = RawNode::default();
        for key in &keys {
            let mut value = BoxElement::<Array>::with_capacity(key.len());
            value.data_slice_mut().copy_from_slice(key);
            root = art.insert_record(root, 0, key, value);
        }
    }

    // #[test]
    fn node_grow() {
        use std::ops::Range;

        fn make_keys(prefix: &str, range: Range<u8>) -> Vec<Vec<u8>> {
            range
                .into_iter()
                .map(|idx| format!("{}{}", prefix, idx).as_bytes().into())
                .collect::<Vec<_>>()
        }

        let mut art = Art::<Array>::new();
        let keys = make_keys("fo", 1..4);

        let mut root = RawNode::default();
        for key in &keys {
            let mut value = BoxElement::<Array>::with_capacity(key.len());
            value.data_slice_mut().copy_from_slice(key);
            root = art.insert_record(root, 0, key, value);
        }

        unsafe {
            for key in &keys {
                let (new_node, record) = art.remove_record(root, 0, key);
                assert!(record.is_some());
                root = new_node;
            }

            let node = match root.as_mut() {
                NodeTypeMut::Node4(node) => node,
                _ => panic!("wrong node type"),
            };
            BoxElement::from_raw(NonNull::from(node));
        }
    }
}