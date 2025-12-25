/// Iterator that yields combinations (cartesian product) one at a time.
pub struct CombinationIter<'a, T: Clone> {
    to_be: &'a [Vec<T>],
    max_range: Vec<usize>,
    total: usize,
    idx: usize,
}

impl<'a, T: Clone> CombinationIter<'a, T> {
    pub fn new(to_be: &'a Vec<Vec<T>>) -> Self {
        let max_range: Vec<usize> = to_be.iter().map(|v| v.len()).collect();

        if max_range.iter().any(|&r| r == 0) {
            return CombinationIter {
                to_be,
                max_range,
                total: 0,
                idx: 0,
            };
        }

        let mut total: usize = 1;
        for &r in &max_range {
            if let Some(prod) = total.checked_mul(r) {
                total = prod;
            } else {
                return CombinationIter {
                    to_be,
                    max_range,
                    total: 0,
                    idx: 0,
                };
            }
        }

        CombinationIter {
            to_be,
            max_range,
            total,
            idx: 0,
        }
    }
}

impl<'a, T: Clone> Iterator for CombinationIter<'a, T> {
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= self.total {
            return None;
        }
        let mut combi: Vec<T> = Vec::with_capacity(self.to_be.len());
        let mut idx = self.idx;
        for (j, &range) in self.max_range.iter().enumerate() {
            let index = idx % range;
            combi.push(self.to_be[j][index].clone());
            idx /= range;
        }
        self.idx += 1;
        Some(combi)
    }
}

/// Iterator that yields permutations using an iterative Heap's algorithm.
pub struct PermuteIter<T: Clone + std::fmt::Debug> {
    a: Vec<T>,
    c: Vec<usize>,
    i: usize,
    yielded_first: bool,
    n: usize,
}

impl<T: Clone + std::fmt::Debug> PermuteIter<T> {
    pub fn new(to_be: &[T]) -> Self {
        let n = to_be.len();
        PermuteIter {
            a: to_be.to_vec(),
            c: vec![0; n],
            i: 0,
            yielded_first: false,
            n,
        }
    }

    pub fn len(&self) -> usize {
        (1..=self.n).product()
    }
}

impl<T: Clone + std::fmt::Debug> Iterator for PermuteIter<T> {
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.yielded_first {
            self.yielded_first = true;
            return Some(self.a.clone());
        }

        while self.i < self.n {
            if self.c[self.i] < self.i {
                if self.i % 2 == 0 {
                    self.a.swap(0, self.i);
                } else {
                    let ci = self.c[self.i];
                    self.a.swap(ci, self.i);
                }
                let res = self.a.clone();
                self.c[self.i] += 1;
                self.i = 0;
                return Some(res);
            } else {
                self.c[self.i] = 0;
                self.i += 1;
            }
        }
        None
    }
}

/// Produce combinations as an iterator.
pub fn combination_iter<'a, T: Clone>(to_be: &'a Vec<Vec<T>>) -> CombinationIter<'a, T> {
    CombinationIter::new(to_be)
}

/// Produce permutations as an iterator.
pub fn permute_iter<T: Clone + std::fmt::Debug>(to_be: &[T]) -> PermuteIter<T> {
    PermuteIter::new(to_be)
}

/// Backwards-compatible: collect the iterator (higher peak memory).
pub fn combination<T: Clone>(toBeCombine: &Vec<Vec<T>>) -> Vec<Vec<T>> {
    combination_iter(toBeCombine).collect()
}

/// Backwards-compatible: collect all permutations.
pub fn permuteAll<T: Clone + std::fmt::Debug>(toBePermute: &[T]) -> Vec<Vec<T>> {
    permute_iter(toBePermute).collect()
}
