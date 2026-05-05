use log::{info, logger, trace};
use smallvec::SmallVec;

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
                    CHC::Clause(head, cond, children) => {
                        let sortedENode =
                            sortNewENode1(&head, &cond, &children, &mut runner.egraph);
                        for permuteChildren in permute_iter(&children) {
                            let permuteENode = CHC::Clause(
                                head.clone(),
                                cond.clone(),
                                permuteChildren.clone().into(),
                            );
                            let res = runner.egraph.lookup(&permuteENode);
                            if res.is_some() {
                                assert!(res.unwrap().id == id);
                            }

                            let permuteSortedENode =
                                sortNewENode1(&head, &cond, &permuteChildren, &mut runner.egraph);
                            if (sortedENode != permuteSortedENode) {
                                assert_eq!(
                                    sortedENode.weak_shape().0,
                                    permuteSortedENode.weak_shape().0
                                );
                            }
                        }
                    }
                    CHC::Compose(children) => {
                        let sortedChildren = sortAppId(
                            &children.iter().map(|x| x.clone().getAppliedId()).collect(),
                            true,
                            runner.egraph.canonAppIdsCache(),
                        );
                        for permuteChildren in permute_iter(&children) {
                            let sortedPermuteChildren = sortAppId(
                                &permuteChildren
                                    .iter()
                                    .map(|x| x.clone().getAppliedId())
                                    .collect(),
                                true,
                                runner.egraph.canonAppIdsCache(),
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
                        let sortedChildren = sortAppId(
                            &children.iter().map(|x| x.clone().getAppliedId()).collect(),
                            true,
                            runner.egraph.canonAppIdsCache(),
                        );
                        for permuteChildren in permute_iter(&children) {
                            let sortedPermuteChildren = sortAppId(
                                &permuteChildren
                                    .iter()
                                    .map(|x| x.clone().getAppliedId())
                                    .collect(),
                                true,
                                runner.egraph.canonAppIdsCache(),
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

// Test for shapeMut based on the scenario described in proven_proven_get_group_compatible_variants:
// Given c[$x,$y] = c[$y,$x] (eclass has a swap symmetry group),
// shapeMut on f(c[$x,$y], c[$y,$x]) should canonicalize both children to c[$0,$1],
// producing f(c[$0,$1], c[$0,$1]) — the "strong shape".
#[test]
fn testShapeMutSymmetry() {
    initLogger();
    let mut eg = CHCEGraph::default();

    // Use fresh named slots as the "variables" inside c
    let x = Slot::fresh();
    let y = Slot::fresh();

    // Build c[$x, $y] = Eq(intType($x), intType($y))
    let ix = eg.add(&CHC::IntType(x));
    let iy = eg.add(&CHC::IntType(y));
    let c_xy = eg.add(&CHC::Eq(ix.clone(), iy.clone()));

    // Build c[$y, $x] = Eq(intType($y), intType($x))  (slots swapped)
    let c_yx = eg.add(&CHC::Eq(iy.clone(), ix.clone()));

    // Union them: now the eclass has a non-trivial swap symmetry group {id, x<->y}
    eg.union(&c_xy, &c_yx);
    eg.rebuild();

    // Build f(c[$x,$y], c[$y,$x]): Eq as the outer node (non-symmetric container)
    let mut f = CHC::Eq(c_xy.clone(), c_yx.clone());

    info!("before shapeMut");
    info!("f: {f:?}");

    // shapeMut should exploit the swap symmetry of c's eclass to canonicalize
    // both AppliedIds to the same form.
    eg.shapeMut(&mut f);

    info!("after shapeMut");
    info!("f: {f:?}");

    let (out_child1, out_child2) = match &f {
        CHC::Eq(c1, c2) => (c1.clone(), c2.clone()),
        _ => panic!("expected Eq"),
    };

    // Both should point to the same eclass with the same slot mapping —
    // i.e. the strong shape collapses c[$x,$y] and c[$y,$x] to c[$0,$1].
    assert_eq!(
        out_child1, out_child2,
        "shapeMut must canonicalize symmetric children to the same AppliedId"
    );
}

#[test]
fn sortExample() {
    initLogger();

    // let farg2 = Slot::fresh();
    // let farg1 = Slot::fresh();

    // let garg1 = Slot::fresh();
    // let garg2 = Slot::fresh();
    // let y = Slot::fresh();
    // let x = Slot::fresh();

    let farg1 = Slot::fresh();
    let farg2 = Slot::fresh();

    let garg1 = Slot::fresh();
    let garg2 = Slot::fresh();
    let x = Slot::fresh();
    let y = Slot::fresh();

    let appIds = vec![
        AppliedId::new(
            Id(0),
            SlotMap {
                map: SmallVec::from_vec(vec![(farg1, x), (farg2, y)]),
            },
        ),
        AppliedId::new(
            Id(0),
            SlotMap {
                map: SmallVec::from_vec(vec![(farg1, y), (farg2, x)]),
            },
        ),
        AppliedId::new(
            Id(1),
            SlotMap {
                map: SmallVec::from_vec(vec![(garg1, y), (garg2, x)]),
            },
        ),
    ];

    trace!("appIds {appIds:?}");

    let cache = CanonAppIdsCache::default();
    let sorted = sortAppId(&appIds, false, &cache);
}
