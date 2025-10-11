pub fn permute<T: Clone>(toBePermut: Vec<Vec<T>>) -> Vec<Vec<T>> {
    let mut maxRange: Vec<u32> = vec![];
    for i in toBePermut.iter() {
        maxRange.push(i.len() as u32);
    }

    let mut permuteNumber = 1;
    for i in maxRange.iter() {
        permuteNumber *= i;
    }

    let mut out: Vec<Vec<T>> = vec![];
    for mut i in 0..permuteNumber {
        let mut combi: Vec<T> = vec![];
        for (j, range) in maxRange.iter().enumerate() {
            let index = i % range;
            combi.push(toBePermut[j][index as usize].clone());
            i = i / range;
        }
        out.push(combi);
    }

    out
}
