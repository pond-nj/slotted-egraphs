pub fn combination<T: Clone>(toBeCombine: Vec<Vec<T>>) -> Vec<Vec<T>> {
    let mut maxRange: Vec<u32> = vec![];
    for i in toBeCombine.iter() {
        maxRange.push(i.len() as u32);
    }

    let mut combinationNumber = 1;
    for i in maxRange.iter() {
        combinationNumber *= i;
    }

    let mut out: Vec<Vec<T>> = vec![];
    for mut i in 0..combinationNumber {
        let mut combi: Vec<T> = vec![];
        for (j, range) in maxRange.iter().enumerate() {
            let index = i % range;
            combi.push(toBeCombine[j][index as usize].clone());
            i = i / range;
        }
        out.push(combi);
    }

    out
}

pub fn permute<T: Clone + std::fmt::Debug>(toBePermute: &[T]) -> Vec<Vec<T>> {
    if toBePermute.len() == 0 {
        return vec![];
    }
    if toBePermute.len() == 1 {
        return vec![toBePermute.to_vec()];
    }
    let recurResult = permute(&toBePermute[1..]);
    let n = toBePermute[0].clone();
    let mut result = vec![];
    for mut resultBefore in recurResult {
        let len = resultBefore.len();
        for i in 0..len {
            let mut resultBeforeTmp = resultBefore.clone();
            resultBeforeTmp.insert(i, n.clone());
            result.push(resultBeforeTmp);
        }

        resultBefore.push(n.clone());
        result.push(resultBefore);
    }
    result
}
