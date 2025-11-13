use std::cell::RefCell;

use super::*;

use log::debug;

fn minDummy(x: &str, y: &str, z: &str) -> String {
    let syntax = format!("(pred <{x} {y} {z}>)");
    format!("(init min {syntax})")
}

// min(X,Y,Z) <- X< Y, Z=X
// min(X,Y,Z) <- X >= Y, Z=Y
fn minCHC(x: &str, y: &str, z: &str, eg: &mut CHCEGraph) -> AppliedId {
    let syntax = format!("(pred <{x} {y} {z}>)");
    // min(X,Y,Z) <- X< Y, Z=X
    let cond1 = format!("(and <(lt {x} {y}) (eq {z} {x})>)");
    let chc1 = format!("(new {syntax} {cond1} <>)");
    let itf1 = format!("(interface min {syntax} 1)");
    merge(&chc1, &itf1, eg);

    // min(X,Y,Z) <- X >= Y, Z=Y
    let cond2 = format!("(and <(geq {x} {y}) (eq {z} {y})>)");
    let chc2 = format!("(new {syntax} {cond2} <>)");
    let itf2 = format!("(interface min {syntax} 2)");
    merge(&chc1, &itf1, eg);

    id(&format!("(compose <{chc1} {chc2}>)"), eg)
}

fn minLeafDummy(x: &str, y: &str) -> String {
    let syntax = format!("(pred <{x} {y}>)");
    format!("(init minLeaf {syntax})")
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

    // min-leaf(X,Y) <- X=leaf, Y=0
    let cond1 = format!("(and <(eq {y} 0) (eq {x} (leaf))>)");
    let chc1 = format!("(new {syntax} {cond1} <>)");
    let itf1 = format!("(interface minLeaf {syntax} 1)");
    merge(&chc1, &itf1, eg);

    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)
    let cond2 = format!("(and <(eq {x} (binode {a} {l} {r})) (eq {y} (+ {m3} 1))>)");
    let chc2 = format!(
        "(new {syntax} {cond2} <{} {} {}>)",
        minLeafDummy(&l, &m1),
        minLeafDummy(&r, &m2),
        minDummy(&m1, &m2, &m3)
    );
    let itf2 = format!("(interface minLeaf {syntax} 2)");
    merge(&chc2, &itf2, eg);

    id(&format!("(compose <{itf1} {itf2}>)"), eg)
}

fn leafDropDummy(x: &str, y: &str, z: &str) -> String {
    let syntax = format!("(pred <{x} {y} {z}>)");
    format!("(init leafDrop {syntax})")
}

// left-drop(x,y,z) ← y=leaf, z=leaf
// left-drop(x, y ,z) ← x ≤0, y = node(a,L,R), z = node(a,L,R)
// left-drop(x,y,z) ← y= node(a,L,R), x ≥1,N1=x−1, left-drop(N1,L,z)
fn leafDropCHC(x: &str, y: &str, z: &str, count: &mut u32, eg: &mut CHCEGraph) -> AppliedId {
    let syntax = format!("(pred <{x} {y} {z}>)");

    // left-drop(x,y,z) ← y=leaf, z=leaf
    let cond1 = format!("(and <(eq {y} (leaf)) (eq {z} (leaf))>)");
    let chc1 = format!("(new {syntax} {cond1} <>)");
    let itf1 = format!("(interface leafDrop {syntax} 1)");
    let leafDropCHC1Id = merge(&chc1, &itf1, eg);
    debug!("leafDropCHC1Id {:?}", leafDropCHC1Id);

    // left-drop(x, y ,z) ← x ≤0, y = node(a,L,R), z = node(a,L,R)
    let l = generateVarFromCount(count, VarType::Node);
    let r = generateVarFromCount(count, VarType::Node);
    let a = generateVarFromCount(count, VarType::Int);
    let cond2 =
        format!("(and <(leq {x} 0) (eq {y} (binode {a} {l} {r})) (eq {z} (binode {a} {l} {r}))>)");
    let chc2 = format!("(new {syntax} {cond2} <>)");
    let itf2 = format!("(interface leafDrop {syntax} 2)");
    let leafDropCHC2Id = merge(&chc2, &itf2, eg);
    debug!("leafDropCHC2Id {:?}", leafDropCHC2Id);

    // left-drop(x,y,z) ← y= node(a,L,R), x ≥1,N1=x−1, left-drop(N1,L,z)
    let l1 = generateVarFromCount(count, VarType::Node);
    let r1 = generateVarFromCount(count, VarType::Node);
    let a1 = generateVarFromCount(count, VarType::Int);
    let n1 = generateVarFromCount(count, VarType::Int);
    let cond3 = format!("(and <(eq {y} (binode {a1} {l1} {r1})) (geq {x} 1) (eq {n1} (- {x} 1))>)");
    let chc3 = format!("(new {syntax} {cond3} <{}>)", leafDropDummy(&n1, &l1, z));
    let itf3 = format!("(interface leafDrop {syntax} 3)");
    let leafDropCHC3Id = merge(&chc3, &itf3, eg);
    debug!("leafDropCHC3Id {:?}", leafDropCHC3Id);

    id(&format!("(compose <{chc1} {chc2} {chc3}>)"), eg)
}

fn rootDummy(n: &str, t: &str, u: &str, m: &str, k: &str) -> String {
    let syntax = format!("(pred <{n} {t} {u} {m} {k}>)");
    format!("(init root {syntax})")
}

#[test]
fn mainTest() {
    // TODO: how to determine slot type?
    initLogger();
    let mut egOrig = CHCEGraph::default();
    let mut unfoldList = Rc::new(RefCell::new(vec![]));
    let mut count = 0;
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
        let rootCHCId = id(&rootCHC, eg);
        eg.analysis_data_mut(rootCHCId.id)
            .predNames
            .insert("rootCHC".to_string());

        let composeRoot = format!("(compose <{rootCHC}>)");

        let rootDummyId = id(&rootDummy(n, t, u, m, k), eg);
        let rootId = id(&composeRoot, eg);
        eg.union(&rootId, &rootDummyId);

        let x = &generateVarFromCount(&mut count, VarType::Int);
        let y = &generateVarFromCount(&mut count, VarType::Int);
        let z = &generateVarFromCount(&mut count, VarType::Int);

        let minDummyId = id(&minDummy(x, y, z), eg);
        let minId = minCHC(x, y, z, eg);
        eg.union(&minDummyId, &minId);

        let x = &generateVarFromCount(&mut count, VarType::Int);
        let y = &generateVarFromCount(&mut count, VarType::Node);
        let z = &generateVarFromCount(&mut count, VarType::Node);

        let leafDropDummyId = id(&leafDropDummy(x, y, z), eg);
        let leafDropId = leafDropCHC(x, y, z, &mut count, eg);
        eg.union(&leafDropDummyId, &leafDropId);
        let leafDropId = eg.find_applied_id(&leafDropDummyId).id;
        debug!("leafDropId {:?}", leafDropId);

        let x = &generateVarFromCount(&mut count, VarType::Node);
        let y = &generateVarFromCount(&mut count, VarType::Int);

        let minLeafDummyId = id(&minLeafDummy(x, y), eg);
        let minLeafId = minLeafCHC(x, y, &mut count, eg);
        eg.union(&minLeafDummyId, &minLeafId);

        debug!("egraph before run");
        dumpCHCEGraph(&eg);
    }

    // TODO: can we not use mem::take here?
    let mut runner: CHCRunner = Runner::default().with_egraph(egOrig).with_iter_limit(3);
    let report = runner.run(&mut getAllRewrites(&mut unfoldList));
    debug!("report {report:?}");

    println!("egraph after run");
    dumpCHCEGraph(&runner.egraph);

    debug!(
        "egraph after size after {} {}",
        runner.egraph.totalNumberOfEclass(),
        runner.egraph.total_number_of_nodes()
    );

    // checkMinLeafUnfoldWithMin(&mut runner.egraph);
    let newDefineComposeId = checkUnfoldNewDefineExists(&mut runner.egraph);
    checkUnfold2NewDefineWithMinLeaf(newDefineComposeId, &mut runner.egraph);

    // check unfold result
    // 19. new1(N,M,K)←M=0,K=0
    // 20. new1(N,M,K)←N≤0,M=M3+1,K=K3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3), min-leaf(L,K1), min-leaf(R,K2), min(K1,K2,K3)
    // 21. new1(N,M,K)←N≥1,N1=N−1 K=K3+1, left-drop(N1,L,U), min-leaf(U,M), min-leaf(L,K1), min-leaf(R,K2), min(K1,K2,K3)

    // let n = &generateVarFromCount(&mut count, VarType::Int);
    let m = &generateVarFromCount(&mut count, VarType::Int);
    let k = &generateVarFromCount(&mut count, VarType::Int);
    // let syntax = format!("(pred <{n} {m} {k}>)");
    let cond = format!("(and <(eq {k} 0) (eq {m} 0)>)");
    // let chc: String = format!("(new {syntax} {cond} <>)");
    // let res = ematch_all(&runner.egraph, &Pattern::parse(&chc).unwrap());
    let res = ematchQueryall(&runner.egraph, &Pattern::parse(&cond).unwrap());
    assert!(res.len() >= 1);
}

// needs at least two iterations for this to pass
fn checkUnfoldNewDefineExists(eg: &mut CHCEGraph) -> Id {
    // new1(N,M,K)←left-drop(N,T,U), min-leaf(U,M), min-leaf(T,K)
    // new1(N,K,M)←left-drop(N,T,U), min-leaf(U,M), min-leaf(T,K)
    // the head in egraph is new(n, k, m) instead of new(n, m, k)
    let count = &mut 0;
    let n = &generateVarFromCount(count, VarType::Int);
    let m = &generateVarFromCount(count, VarType::Int);
    let k = &generateVarFromCount(count, VarType::Int);
    let t = &generateVarFromCount(count, VarType::Node);
    let u = &generateVarFromCount(count, VarType::Node);

    // define
    let syntax = format!("(pred <{n} {k} {m}>)");
    let chc: String = format!(
        "(new {syntax} (and <>) <{} {} {}>)",
        leafDropDummy(n, t, u),
        minLeafDummy(u, m),
        minLeafDummy(t, k)
    );
    let res = ematchQueryall(&eg, &Pattern::parse(&chc).unwrap());
    assert!(res.len() >= 1);

    let newDefineCompose = format!("(compose <{chc}>)");
    let res = ematchQueryall(&eg, &Pattern::parse(&newDefineCompose).unwrap());
    let newDefineComposeId = res[0].1;
    assert!(res.len() >= 1);

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
    let chc1 = format!(
        "(new {syntax} (and <(eq {t} (leaf)) (eq {u} (leaf))>) <{} {}>)",
        minLeafDummy(u, m),
        minLeafDummy(t, k)
    );
    let res = ematchQueryall(&eg, &Pattern::parse(&chc1).unwrap());
    assert!(res.len() >= 1);

    let a = &generateVarFromCount(count, VarType::Int);
    let l = &generateVarFromCount(count, VarType::Node);
    let r = &generateVarFromCount(count, VarType::Node);

    let chc2 = format!(
        "(new {syntax} (and <(leq {n} 0) (eq {t} (binode {a} {l} {r})) (eq {u} (binode {a} {l} {r}))>) <{} {}>)",
        minLeafDummy(u, m),
        minLeafDummy(t, k)
    );
    let res2 = ematchQueryall(&eg, &Pattern::parse(&chc2).unwrap());
    assert!(res2.len() > 0);

    let a1 = &generateVarFromCount(count, VarType::Int);
    let l1 = &generateVarFromCount(count, VarType::Node);
    let r1 = &generateVarFromCount(count, VarType::Node);

    let n1 = &generateVarFromCount(count, VarType::Int);
    let cond3 = format!("(and <(eq {t} (binode {a1} {l1} {r1})) (geq {n} 1) (eq {n1} (- {n} 1))>)");
    let resCond3 = ematchQueryall(eg, &Pattern::parse(&cond3).unwrap());
    assert!(resCond3.len() > 0);

    let chc3 = format!(
        "(new {syntax} {} <{} {} {}>)",
        cond3,
        leafDropDummy(n1, l1, u),
        minLeafDummy(u, m),
        minLeafDummy(t, k)
    );
    let res3 = ematchQueryall(&eg, &Pattern::parse(&chc3).unwrap());
    assert!(res3.len() > 0);

    let compose = format!("(compose <{chc1} {chc2} {chc3}>)");
    let composeRes = ematchQueryall(&eg, &Pattern::parse(&compose).unwrap());
    assert!(composeRes.len() > 0);
    assert!(composeRes[0].1 == newDefineComposeId);

    return newDefineComposeId;
}

// need at least 3 iterations for this to pass
fn checkUnfold2NewDefineWithMinLeaf(newDefineComposeId: Id, eg: &mut CHCEGraph) {
    // new1(N,K,M)←T = leaf, U = leaf, min-leaf(U,M), min-leaf(T,K)

    // with
    // min-leaf(X,Y) <- X=leaf, Y=0
    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)
    // into

    // new1(N,K,M)←T = leaf, U = leaf, U = leaf, M = 0, min-leaf(T,K)

    // TODO: vvv this is wrong, it should be unfolded with the second clause of minleaf
    // new1(N,K,M)←T = leaf, U = leaf, min-leaf(U,M), T = leaf, K = 0

    let mut count = 0;

    let n = &generateVarFromCount(&mut count, VarType::Int);
    let k = &generateVarFromCount(&mut count, VarType::Int);
    let m = &generateVarFromCount(&mut count, VarType::Int);

    let syntax = format!("(pred <{n} {k} {m}>)");

    let t = &generateVarFromCount(&mut count, VarType::Node);
    let u = &generateVarFromCount(&mut count, VarType::Node);

    let originalCHC = format!(
        "(new {syntax} (and <(eq {t} (leaf)) (eq {u} (leaf))>) <{} {}>)",
        minLeafDummy(u, m),
        minLeafDummy(t, k)
    );
    let res = ematchQueryall(&eg, &Pattern::parse(&originalCHC).unwrap());
    println!("found ENodeTobeUnfolded {:?}", res);
    assert!(res.len() >= 1);

    let composeOriginalCHC = format!("(compose <{originalCHC} *0>)");
    let res = ematchQueryall(&eg, &Pattern::parse(&composeOriginalCHC).unwrap());
    let originalRootId = res[0].1;
    println!("found composeOriginalCHC {:?}", originalRootId);
    assert!(res.len() == 1);

    assert!(newDefineComposeId == originalRootId);

    // unfold_id13_in_id65_using_id55
    let unfoldChc1 = format!(
        "(new {syntax} (and <(eq {t} (leaf)) (eq {u} (leaf)) (eq {u} (leaf)) (eq {m} 0)>) <{}>)",
        minLeafDummy(t, k)
    );
    let res = ematchQueryall(&eg, &Pattern::parse(&unfoldChc1).unwrap());
    println!("found unfoldCHC1 {:?}", res);
    assert!(res.len() >= 1);

    // TODO: this is wrong,
    // let unfoldChc2 = format!(
    //     "(new {syntax} (and <(eq {t} (leaf)) (eq {u} (leaf)) (eq {t} (leaf)) (eq {k} 0)>) <{}>)",
    //     minLeafDummy(u, m)
    // );
    // let res = ematchQueryall(&eg, &Pattern::parse(&unfoldChc2).unwrap());
    // println!("found unfoldCHC2 {:?}", res);
    // assert!(res.len() >= 1);

    //     let composeCHC = format!("(compose <{unfoldChc1} {unfoldChc2} *0>)");
    //     let res = ematchQueryall(&eg, &Pattern::parse(&composeCHC).unwrap());
    //     println!("found composeCHC {:?}", res);
    //     assert!(res.len() >= 1);

    //     assert!(res[0].1 == originalRootId);
}

fn checkMinLeafUnfoldWithMin(eg: &mut CHCEGraph) {
    // min-leaf(X,Y) <- X=leaf, Y=0
    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), M1 < M2, M3 = M1.
    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), M1 >= M2, M2 = M3.

    let count = &mut 0;
    let x = &generateVarFromCount(count, VarType::Node);
    let y = &generateVarFromCount(count, VarType::Int);

    let a = generateVarFromCount(count, VarType::Int);
    let l = generateVarFromCount(count, VarType::Node);
    let r = generateVarFromCount(count, VarType::Node);
    let m1 = generateVarFromCount(count, VarType::Int);
    let m2 = generateVarFromCount(count, VarType::Int);
    let m3 = generateVarFromCount(count, VarType::Int);

    let syntax = format!("(pred <{x} {y}>)");

    // min-leaf(X,Y) <- X=leaf, Y=0
    let cond1 = format!("(and <(eq {y} 0) (eq {x} (leaf))>)");
    let chc1 = format!("(new {syntax} {cond1} <>)");

    let res1 = ematchQueryall(&eg, &Pattern::parse(&chc1).unwrap());
    assert!(res1.len() > 0);

    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), M1 < M2, M3 = M1.
    let cond2 = format!(
        "(and <(eq {x} (binode {a} {l} {r})) (eq {y} (+ {m3} 1)) (lt {m1} {m2}) (eq {m3} {m1})>)"
    );
    let chc2 = format!(
        "(new {syntax} {cond2} <{} {}>)",
        minLeafDummy(&l, &m1),
        minLeafDummy(&r, &m2),
    );
    let res2 = ematchQueryall(&eg, &Pattern::parse(&chc2).unwrap());
    assert!(res2.len() > 0);

    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), M1 >= M2, M2 = M3.
    let cond3 = format!(
        "(and <(eq {x} (binode {a} {l} {r})) (eq {y} (+ {m3} 1)) (geq {m1} {m2}) (eq {m2} {m3})>)"
    );
    let resCond3 = ematchQueryall(eg, &Pattern::parse(&cond3).unwrap());
    assert!(resCond3.len() > 0);

    let chc3 = format!(
        "(new {syntax} {cond3} <{} {}>)",
        minLeafDummy(&l, &m1),
        minLeafDummy(&r, &m2),
    );
    let res3 = ematchQueryall(&eg, &Pattern::parse(&chc3).unwrap());
    assert!(res3.len() > 0);

    let unfold = format!("(compose <{chc1} {chc2} {chc3}>)");
    let res = ematchQueryall(&eg, &Pattern::parse(&unfold).unwrap());
    assert!(res.len() > 0);
    assert!(res[0].1 == id(&minLeafDummy(x, y), eg).id);
}

// #[test]
// fn minLeafAndMinTest() {
//     // TODO: how to determine slot type?
//     initLogger();
//     let mut egOrig = CHCEGraph::default();
//     let mut unfoldList = Rc::new(RefCell::new(vec![]));
//     let mut count = 0;
//     {
//         let eg = &mut egOrig;

//         let x = &generateVarFromCount(&mut count, VarType::Int);
//         let y = &generateVarFromCount(&mut count, VarType::Int);
//         let z = &generateVarFromCount(&mut count, VarType::Int);

//         // min(X,Y,Z) <- X< Y, Z=X
//         // min(X,Y,Z) <- X >= Y, Z=Y
//         let minDummyId = id(&minDummy(x, y, z), eg);
//         let minId = minCHC(x, y, z, eg);
//         eg.union(&minDummyId, &minId);

//         let x = &generateVarFromCount(&mut count, VarType::Node);
//         let y = &generateVarFromCount(&mut count, VarType::Int);

//         // min-leaf(X,Y) <- X=leaf, Y=0
//         // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)
//         let minLeafDummyId = id(&minLeafDummy(x, y), eg);
//         let minLeafId = minLeafCHC(x, y, &mut count, eg);
//         eg.union(&minLeafId, &minLeafDummyId);

//         debug!("egraph before run");
//         dumpCHCEGraph(&eg);
//     }

//     let mut runner: CHCRunner = Runner::default().with_egraph(egOrig).with_iter_limit(1);
//     let report = runner.run(&mut getAllRewrites(&mut unfoldList));
//     debug!("report {report:?}");

//     debug!("egraph after run");
//     dumpCHCEGraph(&runner.egraph);

//     checkMinLeafUnfoldWithMin(&mut runner.egraph);
// }
