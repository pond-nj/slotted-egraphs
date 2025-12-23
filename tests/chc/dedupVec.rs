// make a data structure that if exist in list, it's not pushed again

use std::collections::BTreeSet;

#[derive(Debug, Clone)]
pub struct DedupVec<T: Ord + Clone> {
    vec: Vec<T>,
    set: BTreeSet<T>,
}

impl<T: Ord + Clone> DedupVec<T> {
    pub fn new() -> Self {
        Self {
            vec: vec![],
            set: BTreeSet::new(),
        }
    }

    pub fn push(&mut self, x: T) {
        if self.set.contains(&x) {
            return;
        }

        self.vec.push(x.clone());
        self.set.insert(x);
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.vec.iter()
    }

    pub fn len(&self) -> usize {
        self.vec.len()
    }

    pub fn clear(&mut self) {
        self.vec.clear();
        self.set.clear();
    }
}

impl<T: Ord + Clone> Default for DedupVec<T> {
    fn default() -> Self {
        Self::new()
    }
}
