use std::hash::Hash;

use std::collections::HashMap;

pub struct HashUnionFind<T> {
    parent: Vec<usize>,
    map: HashMap<T, usize>,
}

fn find(parent: &mut Vec<usize>, key: usize) -> usize {
    let mut k = key;
    let mut p = parent[k];
    while p != k {
        let pp = parent[p];
        parent[k] = pp;
        k = p;
        p = pp;
    }
    k
}

impl<T: Hash + Eq + Clone> HashUnionFind<T> {
    pub fn new(elems: impl IntoIterator<Item = T>) -> Self {
        let mut map = HashMap::default();
        let mut parent = vec![];
        for elem in elems.into_iter() {
            let j = map.len();
            map.insert(elem, j);
            parent.push(j);
        }
        HashUnionFind { parent, map }
    }

    pub fn find(&mut self, key: usize) -> usize {
        find(&mut self.parent, key)
    }

    pub fn findOrAddE(&mut self, elem: &T) -> usize {
        let Some(key) = self.map.get(elem) else {
            let j = self.map.len();
            self.map.insert(elem.clone(), j);
            self.parent.push(j);
            assert!(self.map.len() == self.parent.len());
            return j;
        };

        self.find(*key)
    }

    pub fn unionE(&mut self, elem1: &T, elem2: &T) -> bool {
        let k1 = self.findOrAddE(elem1);
        let k2 = self.findOrAddE(elem2);
        if k1 == k2 {
            return false;
        }
        self.union(k1, k2)
    }

    pub fn union(&mut self, key0: usize, key1: usize) -> bool {
        let k0 = self.find(key0);
        let k1 = self.find(key1);
        if k0 == k1 {
            return false;
        }

        self.parent[k1] = k0;
        true
    }

    pub fn buildGroups(&mut self) -> Vec<Vec<T>> {
        let mut groups: HashMap<usize, Vec<T>, _> = HashMap::new();
        for (x, y) in self.map.iter() {
            groups
                .entry(find(&mut self.parent, *y))
                .or_insert(vec![])
                .push(x.clone());
        }
        groups.into_values().collect()
    }
}
