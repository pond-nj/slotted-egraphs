fn main() {
    let toBePermut: Vec<Vec<u32>> = vec![vec![11, 12, 13], vec![21, 22, 23], vec![31, 32, 33]];
    let mut maxRange: Vec<u32> = vec![];
    for i in toBePermut.iter() {
        maxRange.push(i.len() as u32);
    }

    let mut permuteNumber = 1;
    for i in maxRange.iter() {
        permuteNumber *= i;
    }

    let mut out: Vec<Vec<u32>> = vec![];
    for mut i in 0..permuteNumber {
        let mut combi: Vec<u32> = vec![];
        for (j, range) in maxRange.iter().enumerate() {
            let index = i % range;
            combi.push(toBePermut[j][index as usize]);
            i = i / range;
        }
        out.push(combi);
    }

    for i in 0..out.len() {
        for j in i + 1..out.len() {
            assert!(out[i] != out[j]);
        }
    }

    println!("{:?}", out);
}
