use log::debug;

pub fn permute<T: Clone + std::fmt::Debug>(toBePermute: &[T]) -> Vec<Vec<T>> {
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

fn main() {
    let toBePermut = vec![1, 2, 3];
    let out = permute(&toBePermut);
    println!("{:?}", out);
}
