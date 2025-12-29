use std::{cell::RefCell, time::Duration};

use super::*;

use log::debug;

macro_rules! checkRes {
    ($res:expr) => {
        assert!(
            $res.len() > 0,
            "res is empty, expected at least one element."
        );

        let allIds = $res.iter().map(|x| &x.1).collect::<BTreeSet<_>>();

        assert!(
            allIds.len() == 1,
            "Expected all elements to have the same ID. Found IDs: {:?}",
            allIds
        );
    };
}

fn minDummy(x: &str, y: &str, z: &str) -> String {
    let syntax = format!("(pred <{x} {y} {z}>)");
    format!("(composeInit min {syntax} (true) <2>)")
}

// min(X,Y,Z) <- X< Y, Z=X
// min(X,Y,Z) <- X >= Y, Z=Y
fn minCHC(x: &str, y: &str, z: &str, eg: &mut CHCEGraph) -> AppliedId {
    let syntax = format!("(pred <{x} {y} {z}>)");
    let syntaxAppId = eg.addExpr(&syntax);
    // min(X,Y,Z) <- X< Y, Z=X
    let cond1 = format!("(and <(lt {x} {y}) (eq {z} {x})>)");
    let chc1 = format!("(new {syntax} {cond1} <>)");
    let chc1AppId = eg.addExpr(&chc1);
    eg.shrink_slots(&chc1AppId, &syntaxAppId.slots(), ());

    // min(X,Y,Z) <- X >= Y, Z=Y
    let cond2 = format!("(and <(geq {x} {y}) (eq {z} {y})>)");
    let chc2 = format!("(new {syntax} {cond2} <>)");
    let chc2AppId = eg.addExpr(&chc2);
    eg.shrink_slots(&chc2AppId, &syntaxAppId.slots(), ());

    let composeAppId = eg.addExpr(&format!("(compose <{chc1} {chc2}>)"));

    eg.analysis_data_mut(composeAppId.id)
        .predNames
        .insert("min".to_string());

    composeAppId
}

fn minLeafDummy(x: &str, y: &str) -> String {
    let syntax = format!("(pred <{x} {y}>)");
    format!("(composeInit minLeaf {syntax} (true) <1>)")
}

// min-leaf(X,Y) <- X=leaf, Y=0
// min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)
fn minLeafCHC(x: &str, y: &str, count: &mut u32, eg: &mut CHCEGraph) -> AppliedId {
    let a = generateVarFromCount(count, VarType::Int);
    let l = generateVarFromCount(count, VarType::Node);
    let r = generateVarFromCount(count, VarType::Node);
    let m1 = generateVarFromCount(count, VarType::Int);
    let m2 = generateVarFromCount(count, VarType::Int);
    let m3 = generateVarFromCount(count, VarType::Int);

    let syntax = format!("(pred <{x} {y}>)");
    let syntaxAppId = eg.addExpr(&syntax);

    // min-leaf(X,Y) <- X=leaf, Y=0
    let cond1 = format!("(and <(eq {y} 0) (eq {x} (leaf))>)");
    let chc1 = format!("(new {syntax} {cond1} <>)");
    let chc1AppId = eg.addExpr(&chc1);
    eg.shrink_slots(&chc1AppId, &syntaxAppId.slots(), ());

    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)
    let cond2 = format!("(and <(eq {x} (binode {a} {l} {r})) (eq {y} (+ {m3} 1))>)");
    let chc2 = format!(
        "(new {syntax} {cond2} <{} {} {}>)",
        minLeafDummy(&l, &m1),
        minLeafDummy(&r, &m2),
        minDummy(&m1, &m2, &m3)
    );
    let chc2AppId = eg.addExpr(&chc2);
    eg.shrink_slots(&chc2AppId, &syntaxAppId.slots(), ());

    let composeAppId = eg.addExpr(&format!("(compose <{chc1} {chc2}>)"));

    eg.analysis_data_mut(composeAppId.id)
        .predNames
        .insert("minLeaf".to_string());

    composeAppId
}

fn leafDropDummy(x: &str, y: &str, z: &str) -> String {
    let syntax = format!("(pred <{x} {y} {z}>)");
    format!("(composeInit leafDrop {syntax} (true) <2>)")
}

// left-drop(x,y,z) ← y=leaf, z=leaf
// left-drop(x, y ,z) ← x ≤0, y = node(a,L,R), z = node(a,L,R)
// left-drop(x,y,z) ← y= node(a,L,R), x ≥1,N1=x−1, left-drop(N1,L,z)
fn leafDropCHC(x: &str, y: &str, z: &str, count: &mut u32, eg: &mut CHCEGraph) -> AppliedId {
    let syntax = format!("(pred <{x} {y} {z}>)");
    let syntaxAppId = eg.addExpr(&syntax);

    // it is not always the case that variable in the head will appear in the body.
    // left-drop(x,y,z) ← y=leaf, z=leaf
    let cond1 = format!("(and <(eq {y} (leaf)) (eq {z} (leaf))>)");
    let chc1 = format!("(new {syntax} {cond1} <>)");
    let chc1AppId = eg.addExpr(&chc1);
    eg.shrink_slots(&chc1AppId, &syntaxAppId.slots(), ());

    // left-drop(x, y ,z) ← x ≤0, y = node(a,L,R), z = node(a,L,R)
    let l = generateVarFromCount(count, VarType::Node);
    let r = generateVarFromCount(count, VarType::Node);
    let a = generateVarFromCount(count, VarType::Int);
    let cond2 =
        format!("(and <(leq {x} 0) (eq {y} (binode {a} {l} {r})) (eq {z} (binode {a} {l} {r}))>)");
    let chc2 = format!("(new {syntax} {cond2} <>)");
    let chc2AppId = eg.addExpr(&chc2);
    eg.shrink_slots(&chc2AppId, &syntaxAppId.slots(), ());

    // left-drop(x,y,z) ← y= node(a,L,R), x ≥1,N1=x−1, left-drop(N1,L,z)
    let l1 = generateVarFromCount(count, VarType::Node);
    let r1 = generateVarFromCount(count, VarType::Node);
    let a1 = generateVarFromCount(count, VarType::Int);
    let n1 = generateVarFromCount(count, VarType::Int);
    let cond3 = format!("(and <(eq {y} (binode {a1} {l1} {r1})) (geq {x} 1) (eq {n1} (- {x} 1))>)");
    let chc3 = format!("(new {syntax} {cond3} <{}>)", leafDropDummy(&n1, &l1, z));
    let chc3AppId = eg.addExpr(&chc3);
    eg.shrink_slots(&chc3AppId, &syntaxAppId.slots(), ());

    let composeAppId = eg.addExpr(&format!("(compose <{chc1} {chc2} {chc3}>)"));

    eg.analysis_data_mut(composeAppId.id)
        .predNames
        .insert("leafDrop".to_string());

    composeAppId
}

fn rootDummy(n: &str, t: &str, u: &str, m: &str, k: &str) -> String {
    let syntax = format!("(pred <{n} {t} {u} {m} {k}>)");
    format!("(composeInit root {syntax} (false) <>)")
}

fn rootCHC(n: &str, m: &str, k: &str, t: &str, u: &str, eg: &mut CHCEGraph) -> AppliedId {
    //  false ← N≥0,M+N<K, left-drop(N,T,U), min-leaf(U,M), min-leaf(T,K)
    let syntax = "(pred <>)";
    let cond = format!("(and <(geq {n} 0) (lt (+ {m} {n}) {k})>)");
    let rootCHC: String = format!(
        "(new {syntax} {cond} <{} {} {}>)",
        leafDropDummy(n, t, u),
        minLeafDummy(u, m),
        minLeafDummy(t, k)
    );
    let rootCHCId = eg.addExpr(&rootCHC);
    eg.analysis_data_mut(rootCHCId.id)
        .predNames
        .insert("rootCHC".to_string());

    let composeAppId = eg.addExpr(&format!("(compose <{rootCHC}>)"));

    eg.analysis_data_mut(composeAppId.id)
        .predNames
        .insert("rootCHC".to_string());

    composeAppId
}

#[test]
fn mainTest() {
    initLogger();
    let mut egOrig = CHCEGraph::default();
    let mut count = 0;
    let doConstraintRewrite = true;
    {
        let eg = &mut egOrig;

        let n = &generateVarFromCount(&mut count, VarType::Int);
        let t = &generateVarFromCount(&mut count, VarType::Node);
        let u = &generateVarFromCount(&mut count, VarType::Node);
        let m = &generateVarFromCount(&mut count, VarType::Int);
        let k = &generateVarFromCount(&mut count, VarType::Int);

        let rootDummyId = eg.addExpr(&rootDummy(n, t, u, m, k));
        let rootId = rootCHC(n, m, k, t, u, eg);
        eg.union(&rootId, &rootDummyId);

        let x = &generateVarFromCount(&mut count, VarType::Int);
        let y = &generateVarFromCount(&mut count, VarType::Int);
        let z = &generateVarFromCount(&mut count, VarType::Int);

        let minDummyId = eg.addExpr(&minDummy(x, y, z));
        let minId = minCHC(x, y, z, eg);
        eg.union(&minDummyId, &minId);

        let x = &generateVarFromCount(&mut count, VarType::Int);
        let y = &generateVarFromCount(&mut count, VarType::Node);
        let z = &generateVarFromCount(&mut count, VarType::Node);

        let leafDropDummyId = eg.addExpr(&leafDropDummy(x, y, z));
        let leafDropId = leafDropCHC(x, y, z, &mut count, eg);
        eg.union(&leafDropDummyId, &leafDropId);

        let x = &generateVarFromCount(&mut count, VarType::Node);
        let y = &generateVarFromCount(&mut count, VarType::Int);

        let minLeafDummyId = eg.addExpr(&minLeafDummy(x, y));
        let minLeafId = minLeafCHC(x, y, &mut count, eg);
        eg.union(&minLeafDummyId, &minLeafId);

        debug!("egraph before run");
        dumpCHCEGraph(&eg);
    }

    let mut runner: CHCRunner = Runner::default().with_egraph(egOrig).with_iter_limit(3);
    let (report, t): (Report, _) = time(|| {
        runner.run(&mut getAllRewrites(
            RewriteList::default(),
            doConstraintRewrite,
        ))
    });

    println!("use time {t:?}");
    println!("report {report:?}");

    println!("egraph after run");
    dumpCHCEGraph(&runner.egraph);
    runner.egraph.check();

    let (unfold1, unfold2, unfold3, newDefineComposeId) =
        checkUnfoldNewDefineExists(&mut runner.egraph);
    checkUnfold2NewDefineWithMinLeaf(unfold2, unfold3, newDefineComposeId, &mut runner.egraph);
    checkUnfold3NewDefineWithMinLeaf(&mut runner.egraph);

    checkUnfold21NewDefineWithMinLeaf(doConstraintRewrite, &mut runner.egraph);
    checkUnfold31NewDefineWithMinLeaf(doConstraintRewrite, &mut runner.egraph);

    checkUnfold22NewDefineWithMinLeaf(&mut runner.egraph);

    // TODO: check unfold result
    // 19. new1(N,M,K)←M=0,K=0
    // 20. new1(N,M,K)←N≤0,M=M3+1,K=K3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3), min-leaf(L,K1), min-leaf(R,K2), min(K1,K2,K3)
    // 21. new1(N,M,K)←N≥1,N1=N−1 K=K3+1, left-drop(N1,L,U), min-leaf(U,M), min-leaf(L,K1), min-leaf(R,K2), min(K1,K2,K3)
}

#[test]
fn testSortAppId() {
    initLogger();
    let mut egOrig = CHCEGraph::default();
    let mut count = 0;
    let doConstraintRewrite = true;
    {
        let eg = &mut egOrig;

        let n = &generateVarFromCount(&mut count, VarType::Int);
        let t = &generateVarFromCount(&mut count, VarType::Node);
        let u = &generateVarFromCount(&mut count, VarType::Node);
        let m = &generateVarFromCount(&mut count, VarType::Int);
        let k = &generateVarFromCount(&mut count, VarType::Int);

        //  false ← N≥0,M+N<K, left-drop(N,T,U), min-leaf(U,M), min-leaf(T,K)
        let syntax = "(pred <>)";
        let cond = format!("(and <(geq {n} 0) (lt (+ {m} {n}) {k})>)");
        let rootCHC: String = format!(
            "(new {syntax} {cond} <{} {} {}>)",
            leafDropDummy(n, t, u),
            minLeafDummy(u, m),
            minLeafDummy(t, k)
        );
        let rootCHCId = eg.addExpr(&rootCHC);
        eg.analysis_data_mut(rootCHCId.id)
            .predNames
            .insert("rootCHC".to_string());

        let composeRoot = format!("(compose <{rootCHC}>)");

        let rootDummyId = eg.addExpr(&rootDummy(n, t, u, m, k));
        let rootId = eg.addExpr(&composeRoot);
        eg.union(&rootId, &rootDummyId);

        let x = &generateVarFromCount(&mut count, VarType::Int);
        let y = &generateVarFromCount(&mut count, VarType::Int);
        let z = &generateVarFromCount(&mut count, VarType::Int);

        let minDummyId = eg.addExpr(&minDummy(x, y, z));
        let minId = minCHC(x, y, z, eg);
        eg.union(&minDummyId, &minId);

        let x = &generateVarFromCount(&mut count, VarType::Int);
        let y = &generateVarFromCount(&mut count, VarType::Node);
        let z = &generateVarFromCount(&mut count, VarType::Node);

        let leafDropDummyId = eg.addExpr(&leafDropDummy(x, y, z));
        let leafDropId = leafDropCHC(x, y, z, &mut count, eg);
        eg.union(&leafDropDummyId, &leafDropId);
        let leafDropId = eg.find_applied_id(&leafDropDummyId).id;
        debug!("leafDropId {:?}", leafDropId);

        let x = &generateVarFromCount(&mut count, VarType::Node);
        let y = &generateVarFromCount(&mut count, VarType::Int);

        let minLeafDummyId = eg.addExpr(&minLeafDummy(x, y));
        let minLeafId = minLeafCHC(x, y, &mut count, eg);
        eg.union(&minLeafDummyId, &minLeafId);

        println!("egraph before run");
        dumpCHCEGraph(&eg);
    }

    let mut runner: CHCRunner = Runner::default().with_egraph(egOrig).with_iter_limit(3);
    let (report, t): (Report, _) = time(|| {
        runner.run(&mut getAllRewrites(
            RewriteList::default(),
            doConstraintRewrite,
        ))
    });

    println!("egraph after run");
    dumpCHCEGraph(&runner.egraph);
    runner.egraph.check();

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

// need at least 2 iterations for this to pass -> egraph size around 100
fn checkUnfoldNewDefineExists(eg: &mut CHCEGraph) -> (String, String, String, Id) {
    // new1(N,M,K)←left-drop(N,T,U), min-leaf(U,M), min-leaf(T,K)
    // new1(N,K,M)←left-drop(N,T,U), min-leaf(U,M), min-leaf(T,K)
    // the head in egraph is new(n, k, m) instead of new(n, m, k)
    let count = &mut 0;
    let n = &generateVarFromCount(count, VarType::Int);
    let m = &generateVarFromCount(count, VarType::Int);
    let k = &generateVarFromCount(count, VarType::Int);
    let t = &generateVarFromCount(count, VarType::Node);
    let u = &generateVarFromCount(count, VarType::Node);
    let syntax = format!("(pred <{n} {m} {k}>)");

    // unfold
    // new1(N,K,M)←left-drop(N,T,U), min-leaf(U,M), min-leaf(T,K)
    // with
    // left-drop(x,y,z) ← y=leaf, z=leaf
    // left-drop(x, y ,z) ← x ≤0, y = node(a,L,R), z = node(a,L,R)
    // left-drop(x,y,z) ← y= node(a,L,R), x ≥1,N1=x−1, left-drop(N1,L,z)

    // into
    // new1(N,K,M)←T = leaf, U = leaf, min-leaf(U,M), min-leaf(T,K)
    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), min-leaf(U,M), min-leaf(T,K)
    // new1(N,K,M)← T = node(a, L, R), N>= 1, N1=N-1, left-drop(N1, L, U), min-leaf(U,M), min-leaf(T,K)

    // new1(N,K,M) ← T = leaf, U = leaf, min-leaf(U,M), min-leaf(T,K)
    let chc1 = format!(
        "(new {syntax} (and <
(eq {t} (leaf)) 
(eq {u} (leaf))>) <{} {}>)",
        minLeafDummy(u, m),
        minLeafDummy(t, k)
    );
    let res = ematchQueryall(&eg, &Pattern::parse(&chc1).unwrap());
    println!("res: {res:?}");
    checkRes!(res);

    let a = &generateVarFromCount(count, VarType::Int);
    let l = &generateVarFromCount(count, VarType::Node);
    let r = &generateVarFromCount(count, VarType::Node);
    let t = &generateVarFromCount(count, VarType::Node);
    let u = &generateVarFromCount(count, VarType::Node);

    // new1(N,K,M)← N <= 0 , T = node(a, l, r), U = node(a, l, r), min-leaf(U,M), min-leaf(T,K)
    let chc2 = format!(
        "(new {syntax} (and <
(leq {n} 0) 
(eq {t} (binode {a} {l} {r})) 
(eq {u} (binode {a} {l} {r}))>) <{} {}>)",
        minLeafDummy(u, m),
        minLeafDummy(t, k)
    );
    let res2 = ematchQueryall(&eg, &Pattern::parse(&chc2).unwrap());
    println!("res2: {res2:?}");
    checkRes!(res2);

    let a = &generateVarFromCount(count, VarType::Int);
    let l = &generateVarFromCount(count, VarType::Node);
    let r = &generateVarFromCount(count, VarType::Node);
    let t = &generateVarFromCount(count, VarType::Node);
    let u = &generateVarFromCount(count, VarType::Node);
    let n1 = &generateVarFromCount(count, VarType::Int);

    // new1(N,K,M)← T = node(a, L, R), N>= 1, N1=N-1, left-drop(N1, L, U), min-leaf(U,M), min-leaf(T,K)
    let chc3 = format!(
        "(new {syntax} (and <
(eq {t} (binode {a} {l} {r})) 
(geq {n} 1) 
(eq {n1} (- {n} 1))>) <{} {} {}>)",
        leafDropDummy(n1, l, u),
        minLeafDummy(u, m),
        minLeafDummy(t, k)
    );
    let res3 = ematchQueryall(&eg, &Pattern::parse(&chc3).unwrap());
    println!("res3: {res3:?}");
    checkRes!(res3);

    let compose = format!("(compose <{chc1} {chc2} {chc3}>)");
    let composeRes = ematchQueryall(&eg, &Pattern::parse(&compose).unwrap());
    println!("composeRes: {composeRes:?}");
    checkRes!(composeRes);

    return (chc1, chc2, chc3, composeRes[0].1);
}

// need at least 3 iterations for this to pass -> egraph size around 200
fn checkUnfold2NewDefineWithMinLeaf(
    unfold2: String,
    unfold3: String,
    newDefineComposeId: Id,
    eg: &mut CHCEGraph,
) {
    // new1(N,K,M)←T = leaf, U = leaf, min-leaf(U,M), min-leaf(T,K)

    // with
    // min-leaf(X,Y) <- X=leaf, Y=0
    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)

    // into
    // new1(N,K,M)←T = leaf, U = leaf, U = leaf, M = 0, min-leaf(T,K)
    // new1(N,K,M)←T = leaf, U = leaf, U=node(A,L,R), M=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3), min-leaf(T,K)

    let mut count = 0;

    // note: must be ordered like this, because it must meet the passed unfold2 and unfold3
    let n = &generateVarFromCount(&mut count, VarType::Int);
    let m = &generateVarFromCount(&mut count, VarType::Int);
    let k = &generateVarFromCount(&mut count, VarType::Int);

    let syntax = format!("(pred <{n} {m} {k}>)");

    let t = &generateVarFromCount(&mut count, VarType::Node);
    let u = &generateVarFromCount(&mut count, VarType::Node);

    let originalCHC = format!(
        "(new {syntax} 
(and <(eq {t} (leaf)) 
(eq {u} (leaf))>) <{} {}>)",
        minLeafDummy(u, m),
        minLeafDummy(t, k)
    );

    let res = ematchQueryall(&eg, &Pattern::parse(&originalCHC).unwrap());
    println!("found ENodeTobeUnfolded {:?}", res);
    checkRes!(res);

    let composeOriginalCHC = format!("(compose <{originalCHC} {unfold2} {unfold3}>)");
    let res = ematchQueryall(&eg, &Pattern::parse(&composeOriginalCHC).unwrap());
    let originalRootId = res[0].1;
    println!("found composeOriginalCHC {:?}", originalRootId);
    checkRes!(res);

    assert!(newDefineComposeId == originalRootId);

    // unfold_id13_in_id76_using_id55
    // new1(N,K,M)←T = leaf, U = leaf, U = leaf, M = 0, min-leaf(T,K)
    let unfoldChc1 = format!(
        "(new {syntax} (and <(eq {t} (leaf)) (eq {u} (leaf)) (eq {m} 0)>) <{}>)",
        minLeafDummy(t, k)
    );
    let res = ematchQueryall(&eg, &Pattern::parse(&unfoldChc1).unwrap());
    // should be id100
    println!("found unfoldCHC1 {:?}", res);
    checkRes!(res);

    // TODO: if we enabled t and u here, it won't match in composeUnfold because t, u is treated to be global var in compose level.
    // but actually since they don't appear in the head, it should be local var in new level only.
    let t = &generateVarFromCount(&mut count, VarType::Node);
    let u = &generateVarFromCount(&mut count, VarType::Node);
    let a = generateVarFromCount(&mut count, VarType::Int);
    let l = generateVarFromCount(&mut count, VarType::Node);
    let r = generateVarFromCount(&mut count, VarType::Node);
    let m1 = generateVarFromCount(&mut count, VarType::Int);
    let m2 = generateVarFromCount(&mut count, VarType::Int);
    let m3 = generateVarFromCount(&mut count, VarType::Int);

    // unfold_id13_in_id76_using_id60
    // new1(N,K,M)←T = leaf, U = leaf, U=node(A,L,R), M=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3), min-leaf(T,K)
    let unfoldChc2 = format!(
        "(new {syntax} (and <(eq {t} (leaf)) (eq {u} (leaf)) (eq {u} (binode {a} {l} {r})) (eq {m} (+ {m3} 1))>) <{} {} {} {}>)",
        minLeafDummy(&l, &m1),
        minLeafDummy(&r, &m2),
        minDummy(&m1, &m2, &m3),
        minLeafDummy(&t, &k)
    );
    let res2 = ematchQueryall(&eg, &Pattern::parse(&unfoldChc2).unwrap());
    // should be id102
    println!("found unfoldCHC2 {:?}", res2);
    checkRes!(res2);

    let composeUnfoldCHC = format!("(compose <{unfoldChc1} {unfoldChc2} *0>)");
    let res3 = ematchQueryall(&eg, &Pattern::parse(&composeUnfoldCHC).unwrap());
    println!("found composeUnfoldCHC {:?}", res3);
    checkRes!(res3);
    assert!(res3[0].1 == newDefineComposeId);
}

// need at least 3 iterations for this to pass -> egraph size around 200
// clause 20 in the paper
fn checkUnfold21NewDefineWithMinLeaf(doConstraintRewrite: bool, eg: &mut CHCEGraph) {
    // unfold
    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), min-leaf(U,M), min-leaf(T,K)

    // with
    // min-leaf(X,Y) <- X=leaf, Y=0
    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)

    // into
    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), U=leaf, M=0 , min-leaf(T,K)
    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), U=node(A,L,R), M=M3+1,
    //  min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3), min-leaf(T,K)

    let count = &mut 0;
    let n = &generateVarFromCount(count, VarType::Int);
    let k = &generateVarFromCount(count, VarType::Int);
    let m = &generateVarFromCount(count, VarType::Int);

    let syntax = format!("(pred <{n} {m} {k}>)");

    let t = &generateVarFromCount(count, VarType::Node);
    let u = &generateVarFromCount(count, VarType::Node);

    let a = &generateVarFromCount(count, VarType::Int);
    let l = &generateVarFromCount(count, VarType::Node);
    let r = &generateVarFromCount(count, VarType::Node);

    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), min-leaf(U,M), min-leaf(T,K)
    let origChc = format!(
        "(new {syntax} (and <
(leq {n} 0) 
(eq {t} (binode {a} {l} {r})) 
(eq {u} (binode {a} {l} {r}))>) <{} {}>)",
        minLeafDummy(u, m),
        minLeafDummy(t, k)
    );
    let res = ematchQueryall(&eg, &Pattern::parse(&origChc).unwrap());
    // unfold_id10_in_id65_using_id43
    // id77
    // id79
    // unfold_id12_in_id67_using_id45
    println!("unfold21 res: {res:?}");
    checkRes!(res);

    if doConstraintRewrite {
        // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), T = U, min-leaf(U,M), min-leaf(T,K)
        let alterOrigChc1 = format!(
            "(new {syntax} (and <
(leq {n} 0) 
(eq {t} (binode {a} {l} {r})) 
(eq {u} (binode {a} {l} {r})) 
(eq {t} {u})>) <{} {}>)",
            minLeafDummy(u, m),
            minLeafDummy(t, k)
        );
        let alterRes1 = ematchQueryall(&eg, &Pattern::parse(&alterOrigChc1).unwrap());
        println!("unfold21 alterRes1 {alterRes1:?}");
        checkRes!(alterRes1);
        assert!(alterRes1[0].1 == res[0].1);
    }

    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), U=leaf, M=0 , min-leaf(T,K)
    let chc2 = format!(
        "(new {syntax} (and <
(leq {n} 0) 
(eq {t} (binode {a} {l} {r})) 
(eq {u} (binode {a} {l} {r})) 
(eq {u} (leaf)) (eq {m} 0)>) <{} >)",
        minLeafDummy(t, k)
    );
    // unfold_id13_in_id77_using_id55
    // unfold_id16_in_id79_using_id57
    let res2 = ematchQueryall(&eg, &Pattern::parse(&chc2).unwrap());
    println!("unfold21 res2: {res2:?}");
    checkRes!(res2);

    let a = &generateVarFromCount(count, VarType::Int);
    let l = &generateVarFromCount(count, VarType::Node);
    let r = &generateVarFromCount(count, VarType::Node);
    let t = &generateVarFromCount(count, VarType::Node);
    let u = &generateVarFromCount(count, VarType::Node);
    let a1 = &generateVarFromCount(count, VarType::Int);
    let l1 = &generateVarFromCount(count, VarType::Node);
    let r1 = &generateVarFromCount(count, VarType::Node);
    let m1 = &generateVarFromCount(count, VarType::Int);
    let m2 = &generateVarFromCount(count, VarType::Int);
    let m3 = &generateVarFromCount(count, VarType::Int);

    let mut chc3 = None;
    if doConstraintRewrite {
        // can be used to test constructorEqRewrite and dedupFromEqRewrite
        // new1(N,K,M)← N <= 0 , T = node(a, l, r), M=M3+1, min-leaf(l,M1), min-leaf(r,M2), min(M1,M2,M3), min-leaf(T,K)
        chc3 = Some(format!(
            "(new {syntax} (and <
(leq {n} 0)
(eq {t} (binode {a} {l} {r}))
(eq {m} (+ {m3} 1))>) <{} {} {} {}>)",
            minLeafDummy(l, m1),
            minLeafDummy(r, m2),
            minDummy(m1, m2, m3),
            minLeafDummy(t, k)
        ));
        let alterRes3 = ematchQueryall(&eg, &Pattern::parse(&chc3.clone().unwrap()).unwrap());
        println!("unfold21 alterRes3 {alterRes3:?}");
        checkRes!(alterRes3);
    } else {
        // new1(N,K,M)← N <= 0 , T = node(a, l, r), U = node(a, l, r), U=node(a1,l1,r1), M=M3+1,
        //  min-leaf(l1,M1), min-leaf(r1,M2), min(M1,M2,M3), min-leaf(T,K)
        chc3 = Some(format!(
            "(new {syntax} (and <
(leq {n} 0) 
(eq {t} (binode {a} {l} {r})) 
(eq {u} (binode {a} {l} {r})) 
(eq {u} (binode {a1} {l1} {r1})) 
(eq {m} (+ {m3} 1))>) <{} {} {} {}>)",
            minLeafDummy(l1, m1),
            minLeafDummy(r1, m2),
            minDummy(m1, m2, m3),
            minLeafDummy(t, k)
        ));
        let res3 = ematchQueryall(&eg, &Pattern::parse(&chc3.clone().unwrap()).unwrap());
        println!("unfold21 res3: {res3:?}");
        checkRes!(res3);
    }

    let composeUnfold21 = format!("(compose <{chc2} {} *0>)", chc3.unwrap());
    let resCompose = ematchQueryall(&eg, &Pattern::parse(&composeUnfold21).unwrap());
    println!("unfold21 resCompose: {resCompose:?}");
    checkRes!(resCompose);
}

fn checkUnfold22NewDefineWithMinLeaf(eg: &mut CHCEGraph) {
    // unfold
    // new1(N,K,M)← T = node(a, L, R), N>= 1, N1=N-1, left-drop(N1, L, U), min-leaf(U,M), min-leaf(T,K)

    // with
    // min-leaf(X,Y) <- X=leaf, Y=0
    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)

    // into
    // new1(N,K,M)← T = node(a, L, R), N>= 1, N1=N-1, left-drop(N1, L, U), min-leaf(U,M), T = leaf, K = 0
    // new1(N,K,M)← T = node(a, L, R), N>= 1, N1=N-1, left-drop(N1, L, U), min-leaf(U,M),
    //  T=node(A,L,R), K=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)

    let count = &mut 0;
    let n = &generateVarFromCount(count, VarType::Int);
    let k = &generateVarFromCount(count, VarType::Int);
    let m = &generateVarFromCount(count, VarType::Int);

    let syntax = format!("(pred <{n} {m} {k}>)");

    let t = &generateVarFromCount(count, VarType::Node);
    let u = &generateVarFromCount(count, VarType::Node);

    // define
    let syntax = format!("(pred <{n} {m} {k}>)");

    let a1 = &generateVarFromCount(count, VarType::Int);
    let l1 = &generateVarFromCount(count, VarType::Node);
    let r1 = &generateVarFromCount(count, VarType::Node);
    let n1 = &generateVarFromCount(count, VarType::Int);
    let l1 = &generateVarFromCount(count, VarType::Node);

    // new1(N,K,M)← T = node(a, L, R), N>= 1, N1=N-1, left-drop(N1, L, U), min-leaf(U,M), min-leaf(T,K)
    let chc = format!(
        "(new {syntax} (and <(eq {t} (binode {a1} {l1} {r1})) (geq {n} 1) (eq {n1} (- {n} 1))>) <{} {} {}>)",
        leafDropDummy(n1, l1, u),
        minLeafDummy(u, m),
        minLeafDummy(t, k)
    );
    let res = ematchQueryall(&eg, &Pattern::parse(&chc).unwrap());
    println!("unfold22 res: {res:?}");
    checkRes!(res);

    // new1(N,K,M)← T = node(a, L, R), N>= 1, N1=N-1, left-drop(N1, L, U), min-leaf(U,M), T = leaf, K = 0
    let chc2 = format!(
        "(new {syntax} (and <(eq {t} (binode {a1} {l1} {r1})) (geq {n} 1) (eq {n1} (- {n} 1)) (eq {t} (leaf)) (eq {k} 0)>) <{} {}>)",
        leafDropDummy(n1, l1, u),
        minLeafDummy(u, m),
    );
    let res2 = ematchQueryall(&eg, &Pattern::parse(&chc2).unwrap());
    // unfold_id13_in_id78_using_id55
    // id122
    println!("unfold22 res2: {res2:?}");
    checkRes!(res2);

    let a2 = &generateVarFromCount(count, VarType::Int);
    let l2 = &generateVarFromCount(count, VarType::Node);
    let r2 = &generateVarFromCount(count, VarType::Node);
    let m1 = &generateVarFromCount(count, VarType::Int);
    let m2 = &generateVarFromCount(count, VarType::Int);
    let m3 = &generateVarFromCount(count, VarType::Int);

    // new1(N,K,M)← T = node(a, L, R), N>= 1, N1=N-1, left-drop(N1, L, U), min-leaf(U,M),
    //  T=node(A1,L1,R1), K=M3+1, min-leaf(L1,M1), min-leaf(R1,M2), min(M1,M2,M3)
    let chc3 = format!(
        "(new {syntax} (and <(eq {t} (binode {a1} {l1} {r1})) (geq {n} 1) (eq {n1} (- {n} 1)) (eq {t} (binode {a2} {l2} {r2})) (eq {k} (+ {m3} 1))>) <{} {} {} {} {}>)",
        leafDropDummy(n1, l1, u),
        minLeafDummy(u, m),
        minLeafDummy(l2, m1),
        minLeafDummy(r2, m2),
        minDummy(m1, m2, m3),
    );
    let res3 = ematchQueryall(&eg, &Pattern::parse(&chc3).unwrap());
    println!("unfold22 res3: {res3:?}");
    checkRes!(res3);

    let composeUnfold22 = format!("(compose <{chc2} {chc3} *0>)");
    let resCompose = ematchQueryall(&eg, &Pattern::parse(&composeUnfold22).unwrap());
    println!("unfold22 resCompose: {resCompose:?}");
    checkRes!(resCompose);
}

// test pass but with debug enabled (log to stdout), the time is too long
// need at least 4 iterations for this to pass -> egraph size around 743
fn checkUnfold3NewDefineWithMinLeaf(eg: &mut CHCEGraph) {
    // new1(N,K,M)←T = leaf, U = leaf, U = leaf, M = 0, min-leaf(T,K)

    // with
    // min-leaf(X,Y) <- X=leaf, Y=0
    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)

    // into
    // new1(N,K,M)←T = leaf, U = leaf, U = leaf, M = 0, T = leaf, K = 0
    // new1(N,K,M)←T = leaf, U = leaf, U = leaf, M = 0, T = node(A,L,R), K=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)

    let mut count = 0;

    let n = &generateVarFromCount(&mut count, VarType::Int);
    let k = &generateVarFromCount(&mut count, VarType::Int);
    let m = &generateVarFromCount(&mut count, VarType::Int);

    let syntax = format!("(pred <{n} {m} {k}>)");

    let t = &generateVarFromCount(&mut count, VarType::Node);
    let u = &generateVarFromCount(&mut count, VarType::Node);

    // unfold_id13_in_id76_using_id55
    // new1(N,K,M)←T = leaf, U = leaf, U = leaf, M = 0, min-leaf(T,K)
    let fromUnfoldChc1 = format!(
        "(new {syntax} (and <(eq {t} (leaf)) (eq {u} (leaf)) (eq {m} 0)>) <{}>)",
        minLeafDummy(t, k)
    );
    let res = ematchQueryall(&eg, &Pattern::parse(&fromUnfoldChc1).unwrap());
    println!("found fromUnfoldChc1 {:?}", res);
    // should be id100
    checkRes!(res);

    // new1(N,K,M)←T = leaf, U = leaf, U = leaf, M = 0, T = leaf, K = 0
    let toUnfoldChc1 =
        format!("(new {syntax} (and <(eq {u} (leaf)) (eq {m} 0) (eq {t} (leaf)) (eq {k} 0)>) <>)",);
    let toUnfoldChc1Pat: Pattern<CHC> = Pattern::parse(&toUnfoldChc1).unwrap();
    debug!("toUnfoldChc1Pat {toUnfoldChc1Pat:?}");
    let res2 = ematchQueryall(&eg, &Pattern::parse(&toUnfoldChc1).unwrap());
    println!("found toUnfoldChc1 {:?}", res2);
    // should be id199
    checkRes!(res2);

    let t = &generateVarFromCount(&mut count, VarType::Node);
    let u = &generateVarFromCount(&mut count, VarType::Node);
    let a = &generateVarFromCount(&mut count, VarType::Int);
    let l = &generateVarFromCount(&mut count, VarType::Node);
    let r = &generateVarFromCount(&mut count, VarType::Node);
    let m1 = &generateVarFromCount(&mut count, VarType::Int);
    let m2 = &generateVarFromCount(&mut count, VarType::Int);
    let m3 = &generateVarFromCount(&mut count, VarType::Int);
    // new1(N,K,M)←T = leaf, U = leaf, U = leaf, M = 0, T = node(A,L,R), K=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)
    let toUnfoldChc2 = format!(
        "(new {syntax} (and <(eq {t} (leaf)) (eq {u} (leaf)) (eq {m} 0) (eq {t} (binode {a} {l} {r})) (eq {k} (+ {m3} 1))>) <{} {} {}>)",
        minLeafDummy(&l, &m1),
        minLeafDummy(&r, &m2),
        minDummy(&m1, &m2, &m3),
    );
    let res3 = ematchQueryall(&eg, &Pattern::parse(&toUnfoldChc2).unwrap());
    println!("found toUnfoldChc2 {:?}", res3);
    checkRes!(res3);

    let toComposeUnfoldCHC = format!("(compose <{toUnfoldChc1} {toUnfoldChc2} *0>)");
    let res4 = ematchQueryall(&eg, &Pattern::parse(&toComposeUnfoldCHC).unwrap());
    println!("found toComposeUnfoldCHC {:?}", res4);
    checkRes!(res4);
}

// need at least 4 iterations for this to pass -> egraph size around 743
// now needed 5 iterations, because of functionality transformation
fn checkUnfold31NewDefineWithMinLeaf(doConstraintRewrite: bool, eg: &mut CHCEGraph) {
    // unfold
    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), U=node(A,L,R), M=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3), min-leaf(T,K)

    // with
    // min-leaf(X,Y) <- X=leaf, Y=0
    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)

    // into
    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), U=node(A,L,R), M=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3), T=leaf, K=0
    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), U=node(A,L,R), M=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3),
    // T=node(A2,L2,R2), K=M32+1, min-leaf(L2,M12), min-leaf(R2,M22), min(M12,M22,M32)

    let count = &mut 0;
    let n = &generateVarFromCount(count, VarType::Int);
    let k = &generateVarFromCount(count, VarType::Int);
    let m = &generateVarFromCount(count, VarType::Int);

    let syntax = format!("(pred <{n} {m} {k}>)");

    let t = &generateVarFromCount(count, VarType::Node);
    let u = &generateVarFromCount(count, VarType::Node);
    let a = &generateVarFromCount(count, VarType::Int);
    let l = &generateVarFromCount(count, VarType::Node);
    let r = &generateVarFromCount(count, VarType::Node);

    let a1 = &generateVarFromCount(count, VarType::Int);
    let l1 = &generateVarFromCount(count, VarType::Node);
    let r1 = &generateVarFromCount(count, VarType::Node);
    let m1 = &generateVarFromCount(count, VarType::Int);
    let m2 = &generateVarFromCount(count, VarType::Int);
    let m3 = &generateVarFromCount(count, VarType::Int);

    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), U=node(A,L,R), M=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3), min-leaf(T,K)
    let origChc = format!(
        "(new {syntax} 
(and <
(leq {n} 0) 
(eq {t} (binode {a} {l} {r})) 
(eq {u} (binode {a} {l} {r})) 
(eq {u} (binode {a1} {l1} {r1})) 
(eq {m} (+ {m3} 1))>) 
<{} {} {} {}>)",
        minLeafDummy(l1, m1),
        minLeafDummy(r1, m2),
        minDummy(m1, m2, m3),
        minLeafDummy(t, k)
    );
    let res = ematchQueryall(&eg, &Pattern::parse(&origChc).unwrap());
    // // 206
    println!("unfold31 res: {res:?}");
    checkRes!(res);

    let mut chc2: Option<String> = None;
    if doConstraintRewrite {
        // new1(N,K,M)← N <= 0 , T = node(a, L, R), M=M3+1, T=leaf, K=0, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)
        chc2 = Some(format!(
            "(new {syntax} (and <
    (leq {n} 0)
    (eq {t} (binode {a} {l} {r}))
    (eq {m} (+ {m3} 1))
    (eq {t} (leaf))
    (eq {k} 0)
    (eq (leaf) (binode {a} {l} {r}))
    >) <{} {} {}>)",
            minLeafDummy(l, m1),
            minLeafDummy(r, m2),
            minDummy(m1, m2, m3),
        ));
        let alterRes2 = ematchQueryall(&eg, &Pattern::parse(&chc2.unwrap()).unwrap());
        println!("unfold31 alterRes2: {alterRes2:?}");
        checkRes!(alterRes2);
    } else {
        // new1(N,K,M)← N <= 0 , T = node(a, l, r), U = node(a, l, r), U=node(A,L,R), M=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3), T=leaf, K=0
        chc2 = Some(format!(
            "(new {syntax} (and <
    (leq {n} 0)
    (eq {t} (binode {a} {l} {r}))
    (eq {u} (binode {a} {l} {r}))
    (eq {u} (binode {a1} {l1} {r1}))
    (eq {m} (+ {m3} 1))
    (eq {t} (leaf))
    (eq {k} 0)>) <{} {} {}>)",
            minLeafDummy(l1, m1),
            minLeafDummy(r1, m2),
            minDummy(m1, m2, m3),
        ));
        let res2 = ematchQueryall(&eg, &Pattern::parse(&chc2.unwrap()).unwrap());
        println!("unfold31 res2: {res2:?}");
        checkRes!(res2);
    }

    let a = &generateVarFromCount(count, VarType::Int);
    let l = &generateVarFromCount(count, VarType::Node);
    let r = &generateVarFromCount(count, VarType::Node);
    let a1 = &generateVarFromCount(count, VarType::Int);
    let l1 = &generateVarFromCount(count, VarType::Node);
    let r1 = &generateVarFromCount(count, VarType::Node);
    let a2 = &generateVarFromCount(count, VarType::Int);
    let l2 = &generateVarFromCount(count, VarType::Node);
    let r2 = &generateVarFromCount(count, VarType::Node);
    let m12 = &generateVarFromCount(count, VarType::Int);
    let m22 = &generateVarFromCount(count, VarType::Int);
    let m32 = &generateVarFromCount(count, VarType::Int);
    let t = &generateVarFromCount(count, VarType::Node);
    let u = &generateVarFromCount(count, VarType::Node);

    let m1 = &generateVarFromCount(count, VarType::Int);
    let m2 = &generateVarFromCount(count, VarType::Int);
    let m3 = &generateVarFromCount(count, VarType::Int);

    // TODO: this test takes a long time, mayby just search for the condition?
    if doConstraintRewrite {
        // after constraint
        // new1(N,K,M)← N <= 0 , T = node(a, l, r), M=M3+1, K=M32+1,
        // min-leaf(l,M1), min-leaf(r,M2), min(M1,M2,M3), min-leaf(l,M12), min-leaf(r,M22), min(M12,M22,M32)
        let alter1Chc3 = format!(
            "(new {syntax}
        (and <
        (leq {n} 0)
        (eq {t} (binode {a} {l} {r}))
        (eq {m} (+ {m3} 1))
        (eq {k} (+ {m32} 1))>)
        <{} {} {} {} {} {}>)",
            minLeafDummy(l, m1),
            minLeafDummy(r, m2),
            minDummy(m1, m2, m3),
            minLeafDummy(l, m12),
            minLeafDummy(r, m22),
            minDummy(m12, m22, m32),
        );
        let alter1Res3 = ematchQueryall(&eg, &Pattern::parse(&alter1Chc3).unwrap());
        println!("unfold31 alter1Res3: {alter1Res3:?}");
        // id932, unfold_id16_0_in_id206_using_id55
        checkRes!(alter1Res3);

        // after functionality
        let alter2Chc3 = format!(
            "(new {syntax}
        (and <
        (leq {n} 0)
        (eq {t} (binode {a} {l} {r}))
        (eq {m} (+ {m3} 1))
        (eq {k} (+ {m32} 1))
        (eq {m1} {m12})
        (eq {m2} {m22})
        >)
        <{} {} {} {}>)",
            minLeafDummy(l, m1),
            minLeafDummy(r, m2),
            minDummy(m1, m2, m3),
            minDummy(m12, m22, m32),
        );
        let alter2Res3 = ematchQueryall(&eg, &Pattern::parse(&alter2Chc3).unwrap());
        println!("unfold31 alter2Res3: {alter2Res3:?}");
        checkRes!(alter2Res3);

        // after constraint again
        let alter3Chc3 = format!(
            "(new {syntax}
(and <
(leq {n} 0)
(eq {t} (binode {a} {l} {r}))
(eq {m} (+ {m3} 1))
(eq {k} (+ {m32} 1))
>)
<{} {} {} {}>)",
            minLeafDummy(l, m1),
            minLeafDummy(r, m2),
            minDummy(m1, m2, m3),
            minDummy(m1, m2, m32),
        );
        let alter3Res3 = ematchQueryall(&eg, &Pattern::parse(&alter3Chc3).unwrap());
        println!("unfold31 alter3Res3: {alter3Res3:?}");
        checkRes!(alter3Res3);

        // after functionality again
        let alter4Chc3 = format!(
            "(new {syntax}
(and <
(leq {n} 0)
(eq {t} (binode {a} {l} {r}))
(eq {m} (+ {m3} 1))
(eq {k} (+ {m32} 1))
(eq {m3} {m32})
>)
<{} {} {}>)",
            minLeafDummy(l, m1),
            minLeafDummy(r, m2),
            minDummy(m1, m2, m3),
        );
        let alter4Res3 = ematchQueryall(&eg, &Pattern::parse(&alter4Chc3).unwrap());
        println!("unfold31 alter4Res3: {alter4Res3:?}");
        checkRes!(alter4Res3);

        // after constraint again, TODO
        // let alter5Chc3 = format!(
        //     "(new {syntax}
        // (and <
        // (leq {n} 0)
        // (eq {t} (binode {a} {l} {r}))
        // (eq {m} (+ {m3} 1))
        // (eq {k} (+ {m32} 1))
        // (eq {m3} {m32})
        // >)
        // <{} {} {}>)",
        //     minLeafDummy(l, m1),
        //     minLeafDummy(r, m2),
        //     minDummy(m1, m2, m3),
        // );
        // let alter5Res3 = ematchQueryall(&eg, &Pattern::parse(&alter5Chc3).unwrap());
        // println!("unfold31 alter1Res3Functional2: {alter5Res3:?}");
        // checkRes!(alter5Res3);
    } else {
        // new1(N,K,M)← N <= 0 , T = node(a, l, r), U = node(a, l, r), U=node(A,L,R), M=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3),
        // T=node(A2,L2,R2), K=M32+1, min-leaf(L2,M12), min-leaf(R2,M22), min(M12,M22,M32)
        let chc3 = format!(
            "(new {syntax}
(and <
(leq {n} 0)
(eq {t} (binode {a} {l} {r}))
(eq {u} (binode {a} {l} {r}))
(eq {u} (binode {a1} {l1} {r1}))
(eq {m} (+ {m3} 1))
(eq {t} (binode {a2} {l2} {r2}))
(eq {k} (+ {m32} 1))>) <{} {} {} {} {} {}>)",
            minLeafDummy(l1, m1),
            minLeafDummy(r1, m2),
            minDummy(m1, m2, m3),
            minLeafDummy(l2, m12),
            minLeafDummy(r2, m22),
            minDummy(m12, m22, m32),
        );
        let res3 = ematchQueryall(&eg, &Pattern::parse(&chc3).unwrap());
        // unfold_id16_in_id114_using_id62
        println!("unfold31 res3: {res3:?}");
        checkRes!(res3);
    }

    // TODO: this takes a very long time to run, why?
    // let composeUnfold31 = format!("(compose <{chc2} {chc3} *0>)");
    // let resCompose = ematchQueryall(&eg, &Pattern::parse(&composeUnfold31).unwrap());
    // println!("unfold31 resCompose: {resCompose:?}");
    // checkRes!(resCompose);
}
