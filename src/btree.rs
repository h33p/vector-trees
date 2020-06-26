use core::cmp::{Ord, Ordering};
use core::fmt::Debug;
use core::mem;

pub const B: usize = 8;
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

    /// Shifts keys and children right so that there is a space for one at `idx`
    pub fn shift_right(&mut self, idx: usize) {
        debug_assert!(self.cur_keys != MAX_KEYS);

        self.keys[idx..(self.cur_keys + 1)].rotate_right(1);
        if !self.leaf {
            self.children[idx..(self.cur_keys + 2)].rotate_right(1);
        }
        self.cur_keys += 1;
    }

    /// Shifts keys and children right so that there is a space for key at `idx`, and child at `idx + 1`
    pub fn shift_right_rchild(&mut self, idx: usize) {
        debug_assert!(self.cur_keys != MAX_KEYS);

        self.keys[idx..(self.cur_keys + 1)].rotate_right(1);
        if !self.leaf {
            self.children[(idx + 1)..(self.cur_keys + 2)].rotate_right(1);
        }
        self.cur_keys += 1;
    }

    /// Shifts keys and children left to fill in a gap at `idx`
    pub fn shift_left(&mut self, idx: usize) {
        debug_assert!(self.keys[idx].is_none());
        debug_assert!(self.children[idx].is_none());

        self.keys[idx..self.cur_keys].rotate_left(1);
        self.children[idx..(self.cur_keys + 1)].rotate_left(1);
        self.cur_keys -= 1;
    }

    /// Shifts keys and children left to fill in a gap at `idx`, used when the right child is none
    pub fn shift_left_rchild(&mut self, idx: usize) {
        debug_assert!(self.keys[idx].is_none());
        debug_assert!(self.children[idx + 1].is_none());

        self.keys[idx..self.cur_keys].rotate_left(1);
        self.children[(idx + 1)..(self.cur_keys + 1)].rotate_left(1);
        self.cur_keys -= 1;
    }

    fn remove_key(&mut self, key_id: usize) -> (Option<V>, Option<u32>) {
        let key = self.keys[key_id].take();
        let child = self.children[key_id].take();

        self.shift_left(key_id);

        (key, child)
    }

    fn remove_key_rchild(&mut self, key_id: usize) -> (Option<V>, Option<u32>) {
        let key = self.keys[key_id].take();
        let child = self.children[key_id + 1].take();

        self.shift_left_rchild(key_id);

        (key, child)
    }

    pub fn insert_leaf_key(&mut self, idx: usize, key: V) {
        debug_assert!(self.leaf);
        debug_assert!(idx <= self.cur_keys);
        self.shift_right(idx);
        self.keys[idx] = Some(key);
    }

    pub fn insert_node(&mut self, value: V) -> Option<V> {
        let (idx, exact) = self.find_key_id(&value);

        if exact {
            mem::replace(&mut self.keys[idx], Some(value))
        } else {
            self.shift_right(idx);
            self.keys[idx] = Some(value);
            None
        }
    }

    pub fn insert_node_rchild(&mut self, value: V) -> Option<V> {
        let (idx, exact) = self.find_key_id(&value);

        if exact {
            mem::replace(&mut self.keys[idx], Some(value))
        } else {
            self.shift_right_rchild(idx);
            self.keys[idx] = Some(value);
            None
        }
    }

    /// Appends all keys and children of other to the end of `self`, adding `mid` as key in the middle
    pub fn merge(&mut self, mid: V, other: &mut Self) {
        debug_assert!(self.cur_keys + 1 + other.cur_keys <= MAX_KEYS);

        if self.cur_keys > 0 {
            debug_assert!(&mid > self.keys[self.cur_keys - 1].as_ref().unwrap());
        }

        if other.cur_keys > 0 {
            debug_assert!(&mid < other.keys[0].as_ref().unwrap());
        }

        self.keys[self.cur_keys] = Some(mid);

        for i in 0..other.cur_keys {
            self.keys[self.cur_keys + 1 + i] = other.keys[i].take();
        }

        for i in 0..=other.cur_keys {
            self.children[self.cur_keys + 1 + i] = other.children[i].take();
        }

        self.cur_keys += 1 + other.cur_keys;
        other.cur_keys = 0;
    }
}

pub struct BVecTree<V> {
    root: Option<u32>,
    free_head: Option<u32>,
    tree_buf: Vec<BVecTreeNode<V>>,
}

impl<V> Default for BVecTree<V> {
    fn default() -> Self {
        Self {
            root: None,
            free_head: None,
            tree_buf: vec![],
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
        self.free_head = None;
        self.tree_buf.clear();
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

            let (mut idx, exact) = node.find_key_id(&value);

            if exact {
                let ret = mem::replace(&mut node.keys[idx], Some(value));
                return ret;
            } else {
                let child = node.children[idx].unwrap();

                if self.get_node(child).cur_keys == MAX_KEYS {
                    self.split_child(cur_node, idx);

                    match value.cmp(self.get_node(cur_node).keys[idx].as_ref().unwrap()) {
                        Ordering::Greater => {
                            idx += 1;
                        }
                        Ordering::Equal => {
                            return mem::replace(
                                &mut self.get_node_mut(cur_node).keys[idx],
                                Some(value),
                            );
                        }
                        Ordering::Less => {}
                    }
                }

                cur_node = self.get_node(cur_node).children[idx].unwrap();
            }
        }

        self.insert_node(cur_node, value)
    }

    pub fn remove(&mut self, value: &V) -> Option<V> {
        let mut cur_node = self.root;

        while let Some(node_idx) = cur_node {
            let node = self.get_node(node_idx);

            let (idx, exact) = node.find_key_id(value);

            if exact {
                if node.leaf {
                    let ret = self.remove_key(node_idx, idx).0;
                    return ret;
                } else {
                    let left_child = node.children[idx].unwrap();
                    let right_child = node.children[idx + 1].unwrap();

                    if self.get_node(left_child).cur_keys > B - 1 {
                        let mut lr_child = left_child;
                        while !self.get_node(lr_child).leaf {
                            self.ensure_node_degree(lr_child, self.get_node(lr_child).cur_keys);
                            let lr_node = self.get_node(lr_child);
                            lr_child = lr_node.children[lr_node.cur_keys].unwrap();
                        }
                        let (pred, _) =
                            self.remove_key(lr_child, self.get_node(lr_child).cur_keys - 1);
                        return mem::replace(&mut self.get_node_mut(node_idx).keys[idx], pred);
                    } else if self.get_node(right_child).cur_keys > B - 1 {
                        let mut rl_child = right_child;
                        while !self.get_node(rl_child).leaf {
                            self.ensure_node_degree(rl_child, 0);
                            let rl_node = self.get_node(rl_child);
                            rl_child = rl_node.children[0].unwrap();
                        }
                        let (succ, _) = self.remove_key(rl_child, 0);
                        return mem::replace(&mut self.get_node_mut(node_idx).keys[idx], succ);
                    } else {
                        let ret = self.merge_children(node_idx, idx);
                        if cur_node == self.root {
                            self.root = Some(ret);
                        }
                        cur_node = Some(left_child);
                        continue;
                    }
                }
            }

            if !node.leaf {
                let ret = self.ensure_node_degree(node_idx, idx);
                if ret != node_idx {
                    if cur_node == self.root {
                        self.root = Some(ret);
                    }
                    cur_node = Some(ret);
                } else {
                    let node = self.get_node(node_idx);
                    cur_node = node.children[node.find_key_id(value).0];
                }
            } else {
                cur_node = node.children[idx];
            }
        }

        None
    }

    fn remove_key(&mut self, node_id: u32, key_id: usize) -> (Option<V>, Option<u32>) {
        let node = self.get_node_mut(node_id);
        node.remove_key(key_id)
    }

    /// Merge `key_id` child of `parent` with `key_id + 1` child
    ///
    /// Returns new parent
    fn merge_children(&mut self, parent: u32, key_id: usize) -> u32 {
        let parent_node = self.get_node_mut(parent);
        let left_child = parent_node.children[key_id].unwrap();
        let right_child = parent_node.children[key_id + 1].unwrap();

        let (mid, _) = parent_node.remove_key_rchild(key_id);
        let (left_node, right_node) = self.get_two_nodes_mut(left_child, right_child);

        left_node.merge(mid.unwrap(), right_node);

        self.free_node(right_child);

        if self.get_node(parent).cur_keys == 0 {
            self.get_node_mut(parent).children[0] = None;
            self.free_node(parent);
            left_child
        } else {
            parent
        }
    }

    fn ensure_node_degree(&mut self, parent: u32, child_id: usize) -> u32 {
        let parent_node = self.get_node(parent);
        let child_node_id = parent_node.children[child_id].unwrap();
        let child_node = self.get_node(child_node_id);

        if child_node.cur_keys < B {
            if child_id != 0
                && self
                    .get_node(parent_node.children[child_id - 1].unwrap())
                    .cur_keys
                    > B - 1
            {
                let (key, (left, right)) = self.get_key_nodes_mut(parent, child_id - 1);
                let left_key = key.take().unwrap();
                right.insert_node(left_key);
                let (nkey, rchild) = left.remove_key_rchild(left.cur_keys - 1);
                right.children[0] = rchild;
                *key = nkey;
            } else if child_id != parent_node.cur_keys
                && self
                    .get_node(parent_node.children[child_id + 1].unwrap())
                    .cur_keys
                    > B - 1
            {
                let (key, (left, right)) = self.get_key_nodes_mut(parent, child_id);
                let right_key = key.take().unwrap();
                left.insert_node_rchild(right_key);
                let (nkey, lchild) = right.remove_key(0);
                left.children[left.cur_keys] = lchild;
                *key = nkey;
            } else if child_id > 0 {
                return self.merge_children(parent, child_id - 1);
            } else {
                return self.merge_children(parent, child_id);
            }
        }

        parent
    }

    fn split_child(&mut self, parent: u32, child_id: usize) {
        let node_to_split = self.get_node(parent).children[child_id].unwrap();
        let new_node = self.allocate_node();

        let (left, right) = self.get_two_nodes_mut(node_to_split, new_node);

        //Copy the second half of node_to_split over to new_node
        for i in 0..(B - 1) {
            right.keys[i] = left.keys[i + B].take();
        }

        let mid = left.keys[B - 1].take().unwrap();

        left.cur_keys = B - 1;
        right.cur_keys = B - 1;

        if left.leaf {
            right.leaf = true;
        } else {
            for i in 0..B {
                right.children[i] = left.children[i + B].take();
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
        self.get_node_mut(node_id).insert_node(value)
    }

    fn get_node_mut(&mut self, id: u32) -> &mut BVecTreeNode<V> {
        self.tree_buf.get_mut(id as usize).unwrap()
    }

    /// Returns 2 individual mutable nodes
    fn get_two_nodes_mut(
        &mut self,
        left: u32,
        right: u32,
    ) -> (&mut BVecTreeNode<V>, &mut BVecTreeNode<V>) {
        debug_assert!(left != right);

        if left < right {
            let (_, br) = self.tree_buf.split_at_mut(left as usize);
            let (left_ret, right_side) = br.split_first_mut().unwrap();
            let (_, br) = right_side.split_at_mut((right - left - 1) as usize);
            let (right_ret, _) = br.split_first_mut().unwrap();
            (left_ret, right_ret)
        } else {
            let (_, br) = self.tree_buf.split_at_mut(right as usize);
            let (right_ret, right_side) = br.split_first_mut().unwrap();
            let (_, br) = right_side.split_at_mut((left - right - 1) as usize);
            let (left_ret, _) = br.split_first_mut().unwrap();
            (left_ret, right_ret)
        }
    }

    fn get_key_nodes_mut(
        &mut self,
        parent: u32,
        key: usize,
    ) -> (&mut Option<V>, (&mut BVecTreeNode<V>, &mut BVecTreeNode<V>)) {
        let parent_node = self.get_node_mut(parent);
        let left = parent_node.children[key].unwrap();
        let right = parent_node.children[key + 1].unwrap();
        debug_assert!(left != parent);
        debug_assert!(right != parent);
        // This is safe, because parent can not be equal to either of the child nodes
        let key_mut = unsafe { &mut *(&mut parent_node.keys[key] as *mut _) };
        (key_mut, self.get_two_nodes_mut(left, right))
    }

    fn get_node(&self, id: u32) -> &BVecTreeNode<V> {
        self.tree_buf.get(id as usize).unwrap()
    }

    fn allocate_node(&mut self) -> u32 {
        if let Some(idx) = self.free_head {
            let free_node = self.get_node_mut(idx);
            let child_zero = free_node.children[0];
            *free_node = BVecTreeNode::default();
            self.free_head = child_zero;
            idx
        } else {
            let ret = self.tree_buf.len() as u32;
            self.tree_buf.push(BVecTreeNode::default());
            ret
        }
    }

    fn free_node(&mut self, node_id: u32) {
        let head = self.free_head;
        let node = self.get_node_mut(node_id);

        //Make sure all the keys and children are taken out before freeing
        debug_assert!(node.keys.iter().filter_map(|x| x.as_ref()).count() == 0);
        debug_assert!(node.children.iter().filter_map(|x| x.as_ref()).count() == 0);

        node.children[0] = head;
        self.free_head = Some(node_id);
    }

    pub fn print_tree(&self) {
        if let Some(idx) = self.root {
            self.print_tree_internal(idx, 0);
        }
    }

    fn print_tree_internal(&self, cur_node: u32, indent: usize) {
        print!("{:02} ", cur_node);
        for _ in 0..indent {
            print!("===");
        }

        let node = self.get_node(cur_node);

        for i in node.keys.iter().take(node.cur_keys) {
            print!("{:?} ", i);
        }

        println!("|");

        if !node.leaf {
            node.children
                .iter()
                .take(node.cur_keys + 1)
                .for_each(|x| self.print_tree_internal(x.unwrap(), indent + 1));
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::BVecTree;
    use rand::{seq::SliceRandom, Rng, SeedableRng};
    use rand_xorshift::XorShiftRng;
    use std::collections::BTreeSet;

    #[test]
    fn test_random_add() {
        for _ in 0..200 {
            let seed = rand::thread_rng().gen_range(0, !0u64);
            println!("Seed: {:x}", seed);

            let mut rng: XorShiftRng = SeedableRng::seed_from_u64(seed);

            let entries: Vec<_> = (0..1000).map(|_| rng.gen_range(0, 50000usize)).collect();
            let entries_s: Vec<_> = (0..1000).map(|_| rng.gen_range(0, 50000usize)).collect();

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

    #[test]
    fn test_random_remove() {
        for _ in 0..500 {
            let seed = rand::thread_rng().gen_range(0, !0u64);
            println!("Seed: {:x}", seed);

            let mut rng: XorShiftRng = SeedableRng::seed_from_u64(seed);

            let entries: Vec<_> = (0..1000).map(|_| rng.gen_range(0, 50000usize)).collect();

            let mut tree = BVecTree::new();
            let mut set = BTreeSet::new();

            for i in entries.iter() {
                set.insert(*i);
                tree.insert(*i);
            }

            let mut entries_r: Vec<_> = set.iter().copied().collect();
            entries_r.shuffle(&mut rng);

            for i in entries_r.iter().take(200) {
                let ret_set = set.remove(&i);
                let ret_tree = tree.remove(&i);

                assert!(
                    ret_tree.is_some() || !ret_set,
                    "{:?} {:?} {:?}",
                    ret_tree,
                    i,
                    tree.contains(&i)
                );
            }

            assert_eq!(tree.iter().count(), set.iter().count());
            assert_eq!(tree.len(), set.len());
        }
    }
}
