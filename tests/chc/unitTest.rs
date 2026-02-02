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

#[test]
fn testSortAppId() {
    initLogger();
    let mut egOrig = CHCEGraph::default();
    let mut count = 0;

    let (rootId, mut runner) = buildLeafDropCHC(egOrig, &mut count);

    let (_, testTime) = time(|| {
        for id in runner.egraph.ids() {
            // test permute and sorted is the same
            for enode in runner.egraph.enodes(id) {
                match enode {
                    CHC::New(syntax, cond, children) => {
                        let sortedENode =
                            sortNewENode1(&syntax, &cond, &children, &mut runner.egraph);
                        for permuteChildren in permute_iter(&children) {
                            let permuteENode = CHC::New(
                                syntax.clone(),
                                cond.clone(),
                                permuteChildren.clone().into(),
                            );
                            let res = runner.egraph.lookup(&permuteENode);
                            if res.is_some() {
                                assert!(res.unwrap().id == id);
                            }

                            let permuteSortedENode =
                                sortNewENode1(&syntax, &cond, &permuteChildren, &mut runner.egraph);
                            if (sortedENode != permuteSortedENode) {
                                assert_eq!(
                                    sortedENode.weak_shape().0,
                                    permuteSortedENode.weak_shape().0
                                );
                            }
                        }
                    }
                    CHC::Compose(children) => {
                        let sortedChildren =
                            sortAppId(&children.iter().map(|x| x.clone().getAppliedId()).collect());
                        for permuteChildren in permute_iter(&children) {
                            let sortedPermuteChildren = sortAppId(
                                &permuteChildren
                                    .iter()
                                    .map(|x| x.clone().getAppliedId())
                                    .collect(),
                            );
                            if (sortedChildren != sortedPermuteChildren) {
                                assert_eq!(
                                    CHC::Compose(
                                        toAppliedIdOrStarVec(sortedChildren.clone()).into()
                                    )
                                    .weak_shape()
                                    .0,
                                    CHC::Compose(
                                        toAppliedIdOrStarVec(sortedPermuteChildren).into()
                                    )
                                    .weak_shape()
                                    .0
                                );
                            }

                            let permuteENode = CHC::Compose(permuteChildren.into());
                            let res = runner.egraph.lookup(&permuteENode);
                            if res.is_some() {
                                assert!(res.unwrap().id == id);
                            }
                        }
                    }
                    CHC::And(children) => {
                        let sortedChildren =
                            sortAppId(&children.iter().map(|x| x.clone().getAppliedId()).collect());
                        for permuteChildren in permute_iter(&children) {
                            let sortedPermuteChildren = sortAppId(
                                &permuteChildren
                                    .iter()
                                    .map(|x| x.clone().getAppliedId())
                                    .collect(),
                            );
                            if (sortedChildren != sortedPermuteChildren) {
                                assert_eq!(
                                    CHC::And(toAppliedIdOrStarVec(sortedChildren.clone()).into())
                                        .weak_shape()
                                        .0,
                                    CHC::And(toAppliedIdOrStarVec(sortedPermuteChildren).into())
                                        .weak_shape()
                                        .0
                                );
                            }

                            let permuteENode = CHC::And(permuteChildren.into());
                            let res = runner.egraph.lookup(&permuteENode);
                            if res.is_some() {
                                assert!(res.unwrap().id == id);
                            }
                        }
                    }
                    _ => {}
                }
            }

            // test permute and added to egraph should be in the same eclass
        }
    });
    println!("testTime {testTime:?}");
}
