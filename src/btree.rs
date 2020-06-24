use core::cmp::{Ord, Ordering};
use core::fmt::Debug;
use core::mem;

pub const B: usize = 16;
pub const MAX_CHILDREN: usize = B * 2;
pub const MAX_KEYS: usize = MAX_CHILDREN - 1;

#[derive(Debug)]
pub struct BVecTreeNode<V> {
    keys: [Option<V>; MAX_KEYS],
    children: [Option<u32>; MAX_CHILDREN],
    cur_keys: usize,
    leaf: bool,
}

impl<V> Default for BVecTreeNode<V> {
    fn default() -> Self {
        Self {
            keys: Default::default(),
            children: Default::default(),
            cur_keys: 0,
            leaf: false,
        }
    }
}

impl<V: Ord> BVecTreeNode<V> {
    pub fn find_key_id(&self, value: &V) -> (usize, bool) {
        //Binary search is simply slower when optimized
        /*match self
            .keys[..self.cur_keys]
            .binary_search_by(|key| value.cmp(key.as_ref().unwrap())) {
            Ok(idx) => (idx, true),
            Err(idx) => (idx, false)
        }*/

        let keys = &self.keys[..self.cur_keys];

        for (i, item) in keys.iter().enumerate().take(self.cur_keys) {
            match value.cmp(item.as_ref().unwrap()) {
                Ordering::Greater => {}
                Ordering::Equal => {
                    return (i, true);
                }
                Ordering::Less => {
                    return (i, false);
                }
            }
        }
        (self.cur_keys, false)
    }
}

pub struct BVecTree<V> {
    root: Option<u32>,
    tree_buf: Vec<BVecTreeNode<V>>,
    free_nodes: Vec<u32>,
}

impl<V> Default for BVecTree<V> {
    fn default() -> Self {
        Self {
            root: None,
            tree_buf: vec![],
            free_nodes: vec![],
        }
    }
}

impl<V: Ord + Debug> BVecTree<V> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn iter(&self) -> impl Iterator<Item = &V> {
        self.tree_buf
            .iter()
            .flat_map(|x| x.keys.iter().filter_map(|x| x.as_ref()))
    }

    pub fn node_iter(&self) -> impl Iterator<Item = &BVecTreeNode<V>> {
        self.tree_buf.iter()
    }

    pub fn len(&self) -> usize {
        self.iter().count()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn clear(&mut self) {
        self.root = None;
        self.tree_buf.clear();
        self.free_nodes.clear();
    }

    pub fn height(&self) -> usize {
        if let Some(idx) = self.root {
            let mut ret = 1;

            let mut cur_node = idx;

            while !self.get_node(cur_node).leaf {
                cur_node = self.get_node(cur_node).children[0].unwrap();
                ret += 1
            }

            ret
        } else {
            0
        }
    }

    pub fn contains(&self, value: &V) -> bool {
        if let Some(idx) = self.root {
            let mut cur_node = idx;

            loop {
                let node = self.get_node(cur_node);

                let (idx, exact) = node.find_key_id(value);

                if exact {
                    return true;
                }

                if node.leaf {
                    break;
                }

                cur_node = node.children[idx].unwrap();
            }
        }

        false
    }

    pub fn insert(&mut self, value: V) -> Option<V> {
        if let Some(idx) = self.root {
            let root_node = self.get_node_mut(idx);

            if root_node.cur_keys == MAX_KEYS {
                let new_root = self.allocate_node();
                let new_root_node = self.get_node_mut(new_root);
                new_root_node.children[0] = Some(idx);
                self.root = Some(new_root);
                self.split_child(new_root, 0);
            }
        } else {
            self.root = Some(self.allocate_node());
            self.get_node_mut(self.root.unwrap()).leaf = true;
        }

        let mut cur_node = self.root.unwrap();

        loop {
            let node = self.get_node_mut(cur_node);

            if node.leaf {
                break;
            }

            let (idx, exact) = node.find_key_id(&value);

            if exact {
                let ret = mem::replace(&mut node.keys[idx], Some(value));
                return ret;
            } else {
                let child = node.children[idx].unwrap();

                if self.get_node(child).cur_keys == MAX_KEYS {
                    self.split_child(cur_node, idx);
                    //TODO: Possibly optimize this to not continue
                    /*match value.cmp(self.get_node(cur_node).keys[idx].as_ref().unwrap()) {
                        Ordering::Less => { idx += 1; },
                        Ordering::Equal => { break; },
                        Ordering::Greater => {}
                    }*/

                    continue;
                }

                cur_node = self.get_node(cur_node).children[idx].unwrap();
            }
        }

        self.insert_node(cur_node, value)
    }

    fn split_child(&mut self, parent: u32, child_id: usize) {
        let node_to_split = self.get_node(parent).children[child_id].unwrap();

        let new_node = self.allocate_node();

        //Copy the second half of node_to_split over to new_node
        for i in 0..(B - 1) {
            self.get_node_mut(new_node).keys[i] =
                self.get_node_mut(node_to_split).keys[i + B].take();
        }

        let mid = self.get_node_mut(node_to_split).keys[B - 1].take().unwrap();

        self.get_node_mut(node_to_split).cur_keys = B - 1;
        self.get_node_mut(new_node).cur_keys = B - 1;

        if self.get_node(node_to_split).leaf {
            self.get_node_mut(new_node).leaf = true;
        } else {
            for i in 0..B {
                self.get_node_mut(new_node).children[i] =
                    self.get_node_mut(node_to_split).children[i + B].take();
            }
        }

        self.insert_node(parent, mid);

        debug_assert!(self.get_node(parent).children[child_id].is_none());
        debug_assert!(self.get_node(parent).children[child_id + 1].is_some());
        let right_child = self.get_node_mut(parent).children[child_id + 1].take();
        self.get_node_mut(parent).children[child_id] = right_child;
        self.get_node_mut(parent).children[child_id + 1] = Some(new_node);
    }

    fn insert_node(&mut self, node_id: u32, value: V) -> Option<V> {
        let (idx, exact) = self.get_node(node_id).find_key_id(&value);

        if exact {
            mem::replace(&mut self.get_node_mut(node_id).keys[idx], Some(value))
        } else {
            let node_mut = self.get_node_mut(node_id);

            for i in (idx..node_mut.cur_keys).rev() {
                node_mut.keys[i + 1] = node_mut.keys[i].take();
            }

            for i in (idx..=node_mut.cur_keys).rev() {
                node_mut.children[i + 1] = node_mut.children[i].take();
            }

            node_mut.keys[idx] = Some(value);
            node_mut.cur_keys += 1;

            None
        }
    }

    fn get_node_mut(&mut self, id: u32) -> &mut BVecTreeNode<V> {
        self.tree_buf.get_mut(id as usize).unwrap()
    }

    fn get_node(&self, id: u32) -> &BVecTreeNode<V> {
        self.tree_buf.get(id as usize).unwrap()
    }

    fn allocate_node(&mut self) -> u32 {
        if let Some(idx) = self.free_nodes.pop() {
            *self.get_node_mut(idx) = BVecTreeNode::default();
            idx
        } else {
            let ret = self.tree_buf.len() as u32;
            self.tree_buf.push(BVecTreeNode::default());
            ret
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::BVecTree;
    use rand::{Rng, SeedableRng};
    use rand_xorshift::XorShiftRng;
    use std::collections::BTreeSet;

    #[test]
    fn test_random_add() {
        for _ in 0..20 {
            let seed = rand::thread_rng().gen_range(0, !0u64);
            println!("Seed: {:x}", seed);

            let mut rng: XorShiftRng = SeedableRng::seed_from_u64(seed);

            let entries: Vec<_> = (0..10000).map(|_| rng.gen_range(0, 5000000usize)).collect();
            let entries_s: Vec<_> = (0..10000).map(|_| rng.gen_range(0, 5000000usize)).collect();

            let mut tree = BVecTree::new();
            let mut set = BTreeSet::new();

            for i in entries.iter() {
                set.insert(*i);
                tree.insert(*i);
            }

            for i in entries_s.iter() {
                assert_eq!(set.contains(i), tree.contains(i));
            }

            assert_eq!(tree.iter().count(), set.iter().count());
            assert_eq!(tree.len(), set.len());
        }
    }
}
