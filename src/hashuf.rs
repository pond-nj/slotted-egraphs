use std::hash::Hash;

use std::collections::HashMap;

pub struct HashUnionFind<T> {
    parent: Vec<usize>,
    map: HashMap<T, usize>,
}

impl<T: Hash + Eq> HashUnionFind<T> {
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

    pub fn findOrAdd(&mut self, key: usize) -> usize {
        let mut k = key;
        let mut p = self.parent[k];
        while p != k {
            let pp = self.parent[p];
            self.parent[k] = pp;
            k = p;
            p = pp;
        }
        Some(k)
    }

    pub fn findOrAddE(&mut self, elem: &T) -> usize {
        let Some(key) = self.map.get(elem) else {
            let j = self.map.len();
            self.map.insert(elem.clone(), j);
        };

        self.find(*key)
    }

    fn unionE(&mut self, elem1: &T, elem2: &T) -> bool {
        let k1 = self.findOrAddE(elem1);
        let k2 = self.findOrAddE(elem2);
        if k1 == k2 {
            return false;
        }
        self.union(k1.unwrap(), k2.unwrap())
    }

    fn union(&mut self, key0: usize, key1: usize) -> bool {
        let k0 = self.findOrAdd(key0);
        let k1 = self.findOrAdd(key1);
        if k0 == k1 {
            return false;
        }

        self.parent[k1.unwrap()] = k0.unwrap();
        true
    }
}
