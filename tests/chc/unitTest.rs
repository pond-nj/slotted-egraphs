use super::*;
#[test]
fn testComb() {
    let mut arr1 = vec![];
    for j in 0..2 {
        arr1.push(j);
    }
    let mut arr2 = vec![];
    for j in 0..3 {
        arr2.push(j);
    }
    let arr = vec![arr1, arr2];

    let combinationResult = combination_iter(&arr);
    let mut combinationSet = HashSet::new();
    for p in combinationResult {
        combinationSet.insert(p);
    }
    println!("combinationSet {combinationSet:?}");
    assert!(combinationSet.len() == 6);
}

#[test]
fn testPermute() {
    let mut arr = vec![];
    for j in 0..10 {
        arr.push(j);
    }
    let permuteResult = permute_iter(&arr);
    let mut permuteSet = HashSet::new();
    for p in permuteResult {
        permuteSet.insert(p);
    }
    assert!(permuteSet.len() == (1..=10).product());
}
