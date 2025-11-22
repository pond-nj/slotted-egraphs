use std::cell::RefCell;

use super::*;

use log::debug;

fn minDummy(x: &str, y: &str, z: &str) -> String {
    let syntax = format!("(pred <{x} {y} {z}>)");
    format!("(init min {syntax} (true) <2>)")
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
    format!("(init minLeaf {syntax} (true) <1>)")
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
    format!("(init leafDrop {syntax} (true) <2>)")
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
    format!("(init root {syntax} (false) <>)")
}

#[test]
fn mainTest() {
    initLogger();
    let mut egOrig = CHCEGraph::default();
    let mut unfoldList = Rc::new(RefCell::new(vec![]));
    let mut constrRewriteList = Rc::new(RefCell::new(vec![]));
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

    let mut runner: CHCRunner = Runner::default().with_egraph(egOrig).with_iter_limit(4);
    let (report, t): (Report, _) = time(|| runner.run(&mut getAllRewrites(&mut unfoldList, &mut constrRewriteList)));
    println!("use time {t:?}");
    println!("report {report:?}");

    println!("egraph after run");
    dumpCHCEGraph(&runner.egraph);

    debug!(
        "egraph after size after {} {}",
        runner.egraph.totalNumberOfEclass(),
        runner.egraph.total_number_of_nodes()
    );

    // let newDefineComposeId = checkUnfoldNewDefineExists(&mut runner.egraph);
    // checkUnfold2NewDefineWithMinLeaf(newDefineComposeId, &mut runner.egraph);
    // checkUnfold3NewDefineWithMinLeaf(&mut runner.egraph);

    // checkUnfold21NewDefineWithMinLeaf(&mut runner.egraph);
    // TODO: vvv the compose lookup in here takes a very long time to run, why? vvv
    // checkUnfold31NewDefineWithMinLeaf(&mut runner.egraph);

    checkUnfold22NewDefineWithMinLeaf(&mut runner.egraph);

    // TODO: check unfold result
    // 19. new1(N,M,K)←M=0,K=0
    // 20. new1(N,M,K)←N≤0,M=M3+1,K=K3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3), min-leaf(L,K1), min-leaf(R,K2), min(K1,K2,K3)
    // 21. new1(N,M,K)←N≥1,N1=N−1 K=K3+1, left-drop(N1,L,U), min-leaf(U,M), min-leaf(L,K1), min-leaf(R,K2), min(K1,K2,K3)
}

// need at least 2 iterations for this to pass -> egraph size around 100
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
    debug!("defineNewId: {res:?}");
    assert!(res.len() >= 1);
    // id65

    let newDefineCompose = format!("(compose <{chc}>)");
    let res = ematchQueryall(&eg, &Pattern::parse(&newDefineCompose).unwrap());
    let newDefineComposeId = res[0].1;
    debug!("defineComposeId: {newDefineComposeId:?}");
    // id66
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

    // new1(N,K,M)←T = leaf, U = leaf, min-leaf(U,M), min-leaf(T,K)
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

    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), min-leaf(U,M), min-leaf(T,K)
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

    // new1(N,K,M)← T = node(a, L, R), N>= 1, N1=N-1, left-drop(N1, L, U), min-leaf(U,M), min-leaf(T,K)
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

// need at least 3 iterations for this to pass -> egraph size around 200
fn checkUnfold2NewDefineWithMinLeaf(newDefineComposeId: Id, eg: &mut CHCEGraph) {
    // new1(N,K,M)←T = leaf, U = leaf, min-leaf(U,M), min-leaf(T,K)

    // with
    // min-leaf(X,Y) <- X=leaf, Y=0
    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)

    // into
    // new1(N,K,M)←T = leaf, U = leaf, U = leaf, M = 0, min-leaf(T,K)
    // new1(N,K,M)←T = leaf, U = leaf, U=node(A,L,R), M=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3), min-leaf(T,K)

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
    // unfold_id10_in_id65_using_id36
    let res = ematchQueryall(&eg, &Pattern::parse(&originalCHC).unwrap());
    println!("found ENodeTobeUnfolded {:?}", res);
    // should be id 76
    assert!(res.len() >= 1);

    let composeOriginalCHC = format!("(compose <{originalCHC} *0>)");
    let res = ematchQueryall(&eg, &Pattern::parse(&composeOriginalCHC).unwrap());
    let originalRootId = res[0].1;
    println!("found composeOriginalCHC {:?}", originalRootId);
    // should be id 66
    assert!(res.len() >= 1);

    assert!(newDefineComposeId == originalRootId);

    // unfold_id13_in_id76_using_id55
    // new1(N,K,M)←T = leaf, U = leaf, U = leaf, M = 0, min-leaf(T,K)
    let unfoldChc1 = format!(
        "(new {syntax} (and <(eq {t} (leaf)) (eq {u} (leaf)) (eq {u} (leaf)) (eq {m} 0)>) <{}>)",
        minLeafDummy(t, k)
    );
    let res = ematchQueryall(&eg, &Pattern::parse(&unfoldChc1).unwrap());
    // should be id100
    println!("found unfoldCHC1 {:?}", res);
    assert!(res.len() >= 1);

    // TODO: if we enabled t and u here, it won't match in composeUnfold because t, u is treated to be global var in compose level.
    // but actually since they don't appear in the head, it should be local var in new level only.
    // let t = &generateVarFromCount(&mut count, VarType::Node);
    // let u = &generateVarFromCount(&mut count, VarType::Node);
    let a = generateVarFromCount(&mut count, VarType::Int);
    let l = generateVarFromCount(&mut count, VarType::Node);
    let r = generateVarFromCount(&mut count, VarType::Node);
    let m1 = generateVarFromCount(&mut count, VarType::Int);
    let m2 = generateVarFromCount(&mut count, VarType::Int);
    let m3 = generateVarFromCount(&mut count, VarType::Int);

    // TODO: we can eliminate U = leaf and U = node(A,L,R) from unfoldChc2
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
    assert!(res2.len() >= 1);

    let composeUnfoldCHC = format!("(compose <{unfoldChc1} {unfoldChc2} *0>)");
    let res3 = ematchQueryall(&eg, &Pattern::parse(&composeUnfoldCHC).unwrap());
    println!("found composeUnfoldCHC {:?}", res3);
    assert!(res3.len() >= 1);
    assert!(res3[0].1 == newDefineComposeId);
}

// need at least 3 iterations for this to pass -> egraph size around 200
// clause 20 in the paper
fn checkUnfold21NewDefineWithMinLeaf(eg: &mut CHCEGraph) {
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

    let syntax = format!("(pred <{n} {k} {m}>)");

    let t = &generateVarFromCount(count, VarType::Node);
    let u = &generateVarFromCount(count, VarType::Node);

    let a = &generateVarFromCount(count, VarType::Int);
    let l = &generateVarFromCount(count, VarType::Node);
    let r = &generateVarFromCount(count, VarType::Node);

    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), min-leaf(U,M), min-leaf(T,K)
    let origChc = format!(
        "(new {syntax} (and <(leq {n} 0) (eq {t} (binode {a} {l} {r})) (eq {u} (binode {a} {l} {r}))>) <{} {}>)",
        minLeafDummy(u, m),
        minLeafDummy(t, k)
    );
    let res = ematchQueryall(&eg, &Pattern::parse(&origChc).unwrap());
    // unfold_id10_in_id65_using_id43
    // id77
    println!("unfold21 res: {res:#?}");
    assert!(res.len() > 0);

    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), U=leaf, M=0 , min-leaf(T,K)
    let chc2 = format!(
        "(new {syntax} (and <(leq {n} 0) (eq {t} (binode {a} {l} {r})) (eq {u} (binode {a} {l} {r})) (eq {u} (leaf)) (eq {m} 0)>) <{} >)",
        minLeafDummy(t, k)
    );
    // unfold_id13_in_id77_using_id55
    let res2 = ematchQueryall(&eg, &Pattern::parse(&chc2).unwrap());
    println!("unfold21 res2: {res2:#?}");
    assert!(res2.len() > 0);

    // TODO: should this be different a, l, r with before?
    let a1 = &generateVarFromCount(count, VarType::Int);
    let l1 = &generateVarFromCount(count, VarType::Node);
    let r1 = &generateVarFromCount(count, VarType::Node);
    let m1 = &generateVarFromCount(count, VarType::Int);
    let m2 = &generateVarFromCount(count, VarType::Int);
    let m3 = &generateVarFromCount(count, VarType::Int);

    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), U=node(A,L,R), M=M3+1, 
    //  min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3), min-leaf(T,K)
    let chc3 = format!(
        "(new {syntax} (and <(leq {n} 0) (eq {t} (binode {a} {l} {r})) (eq {u} (binode {a} {l} {r})) (eq {u} (binode {a1} {l1} {r1})) (eq {m} (+ {m3} 1))>) <{} {} {} {}>)",
        minLeafDummy(l1, m1), 
        minLeafDummy(r1, m2),
        minDummy(m1, m2, m3),
        minLeafDummy(t, k)
    );
    let res3 = ematchQueryall(&eg, &Pattern::parse(&chc3).unwrap());
    println!("unfold21 res3: {res3:#?}");
    assert!(res3.len() > 0);

    let composeUnfold21 = format!("(compose <{chc2} {chc3} *0>)");
    let resCompose = ematchQueryall(&eg, &Pattern::parse(&composeUnfold21).unwrap());
    println!("unfold21 resCompose: {resCompose:#?}");
    assert!(resCompose.len() > 0);
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

    let syntax = format!("(pred <{n} {k} {m}>)");

    let t = &generateVarFromCount(count, VarType::Node);
    let u = &generateVarFromCount(count, VarType::Node);

    // define
    let syntax = format!("(pred <{n} {k} {m}>)");

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
    println!("unfold22 res: {res:#?}");
    assert!(res.len() > 0);

    // new1(N,K,M)← T = node(a, L, R), N>= 1, N1=N-1, left-drop(N1, L, U), min-leaf(U,M), T = leaf, K = 0
    let chc2 = format!(
        "(new {syntax} (and <(eq {t} (binode {a1} {l1} {r1})) (geq {n} 1) (eq {n1} (- {n} 1)) (eq {t} (leaf)) (eq {k} 0)>) <{} {}>)",
        leafDropDummy(n1, l1, u),
        minLeafDummy(u, m),
    );
    let res2 = ematchQueryall(&eg, &Pattern::parse(&chc2).unwrap());
    // unfold_id13_in_id78_using_id55
    // id122
    println!("unfold22 res2: {res2:#?}");
    assert!(res2.len() > 0);

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
    println!("unfold22 res3: {res3:#?}");
    assert!(res3.len() > 0);

    let composeUnfold22 = format!("(compose <{chc2} {chc3} *0>)");
    let resCompose = ematchQueryall(&eg, &Pattern::parse(&composeUnfold22).unwrap());
    println!("unfold22 resCompose: {resCompose:#?}");
    assert!(resCompose.len() > 0); 
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

    let syntax = format!("(pred <{n} {k} {m}>)");

    let t = &generateVarFromCount(&mut count, VarType::Node);
    let u = &generateVarFromCount(&mut count, VarType::Node);

    // unfold_id13_in_id76_using_id55
    // new1(N,K,M)←T = leaf, U = leaf, U = leaf, M = 0, min-leaf(T,K)
    let fromUnfoldChc1 = format!(
        "(new {syntax} (and <(eq {t} (leaf)) (eq {u} (leaf)) (eq {u} (leaf)) (eq {m} 0)>) <{}>)",
        minLeafDummy(t, k)
    );
    let res = ematchQueryall(&eg, &Pattern::parse(&fromUnfoldChc1).unwrap());
    println!("found fromUnfoldChc1 {:?}", res);
    // should be id100
    assert!(res.len() >= 1);

    // new1(N,K,M)←T = leaf, U = leaf, U = leaf, M = 0, T = leaf, K = 0
    let toUnfoldChc1 = format!(
        "(new {syntax} (and <(eq {t} (leaf)) (eq {u} (leaf)) (eq {u} (leaf)) (eq {m} 0) (eq {t} (leaf)) (eq {k} 0)>) <>)",
    );
    let toUnfoldChc1Pat: Pattern<CHC> = Pattern::parse(&toUnfoldChc1).unwrap();
    debug!("toUnfoldChc1Pat {toUnfoldChc1Pat:#?}");
    let res2 = ematchQueryall(&eg, &Pattern::parse(&toUnfoldChc1).unwrap());
    println!("found toUnfoldChc1 {:?}", res2);
    // should be id199
    assert!(res2.len() >= 1);

    let a = &generateVarFromCount(&mut count, VarType::Int);
    let l = &generateVarFromCount(&mut count, VarType::Node);
    let r = &generateVarFromCount(&mut count, VarType::Node);
    let m1 = &generateVarFromCount(&mut count, VarType::Int);
    let m2 = &generateVarFromCount(&mut count, VarType::Int);
    let m3 = &generateVarFromCount(&mut count, VarType::Int);
    // new1(N,K,M)←T = leaf, U = leaf, U = leaf, M = 0, T = node(A,L,R), K=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)
    let toUnfoldChc2 = format!(
        "(new {syntax} (and <(eq {t} (leaf)) (eq {u} (leaf)) (eq {u} (leaf)) (eq {m} 0) (eq {t} (binode {a} {l} {r})) (eq {k} (+ {m3} 1))>) <{} {} {}>)",
        minLeafDummy(&l, &m1),
        minLeafDummy(&r, &m2),
        minDummy(&m1, &m2, &m3),
    );
    let res3 = ematchQueryall(&eg, &Pattern::parse(&toUnfoldChc2).unwrap());
    println!("found toUnfoldChc2 {:?}", res3);
    assert!(res3.len() >= 1);

    let toComposeUnfoldCHC = format!("(compose <{toUnfoldChc1} {toUnfoldChc2} *0>)");
    let res4 = ematchQueryall(&eg, &Pattern::parse(&toComposeUnfoldCHC).unwrap());
    println!("found toComposeUnfoldCHC {:?}", res4);
    assert!(res4.len() >= 1);
}

// need at least 4 iterations for this to pass -> egraph size around 743
fn checkUnfold31NewDefineWithMinLeaf(eg: &mut CHCEGraph) {
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

    let syntax = format!("(pred <{n} {k} {m}>)");

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
        "(new {syntax} (and <(leq {n} 0) (eq {t} (binode {a} {l} {r})) (eq {u} (binode {a} {l} {r})) (eq {u} (binode {a1} {l1} {r1})) (eq {m} (+ {m3} 1))>) <{} {} {} {}>)",
        minLeafDummy(l1, m1), 
        minLeafDummy(r1, m2),
        minDummy(m1, m2, m3),
        minLeafDummy(t, k)
    );
    let res = ematchQueryall(&eg, &Pattern::parse(&origChc).unwrap());
    println!("unfold31 res: {res:#?}");
    assert!(res.len() > 0);

    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), U=node(A,L,R), M=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3), T=leaf, K=0
    let chc2 = format!(
        "(new {syntax} (and <(leq {n} 0) (eq {t} (binode {a} {l} {r})) (eq {u} (binode {a} {l} {r})) (eq {u} (binode {a1} {l1} {r1})) (eq {m} (+ {m3} 1)) (eq {t} (leaf)) (eq {k} 0)>) <{} {} {}>)",
        minLeafDummy(l1, m1), 
        minLeafDummy(r1, m2),
        minDummy(m1, m2, m3),
    );
    let res2 = ematchQueryall(&eg, &Pattern::parse(&chc2).unwrap());
    println!("unfold31 res2: {res2:#?}");
    assert!(res2.len() > 0);

    let a2 = &generateVarFromCount(count, VarType::Int);
    let l2 = &generateVarFromCount(count, VarType::Node);
    let r2 = &generateVarFromCount(count, VarType::Node);
    let m12 = &generateVarFromCount(count, VarType::Int);
    let m22 = &generateVarFromCount(count, VarType::Int);
    let m32 = &generateVarFromCount(count, VarType::Int);

    // TODO: test functionality transformation here
    // new1(N,K,M)← N <= 0 , T = node(a, L, R), U = node(a, l, r), U=node(A,L,R), M=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3), 
    // T=node(A2,L2,R2), K=M32+1, min-leaf(L2,M12), min-leaf(R2,M22), min(M12,M22,M32)
    let chc3 = format!(
        "(new {syntax} (and <(leq {n} 0) (eq {t} (binode {a} {l} {r})) (eq {u} (binode {a} {l} {r})) (eq {u} (binode {a1} {l1} {r1})) (eq {m} (+ {m3} 1)) (eq {t} (binode {a2} {l2} {r2})) (eq {k} (+ {m32} 1))>) <{} {} {} {} {} {}>)",
        minLeafDummy(l1, m1), 
        minLeafDummy(r1, m2),
        minDummy(m1, m2, m3),
        minLeafDummy(l2, m12), 
        minLeafDummy(r2, m22),
        minDummy(m12, m22, m32),
    );
    let res3 = ematchQueryall(&eg, &Pattern::parse(&chc3).unwrap());
    println!("unfold31 res3: {res3:#?}");
    assert!(res3.len() > 0);

    // TODO: this takes a very long time to run, why?
    // let composeUnfold31 = format!("(compose <{chc2} {chc3} *0>)");
    // let resCompose = ematchQueryall(&eg, &Pattern::parse(&composeUnfold31).unwrap());
    // println!("unfold31 resCompose: {resCompose:#?}");
    // assert!(resCompose.len() > 0);
}

// fn checkMinLeafUnfoldWithMin(eg: &mut CHCEGraph) {
//     // min-leaf(X,Y) <- X=leaf, Y=0
//     // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), M1 < M2, M3 = M1.
//     // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), M1 >= M2, M2 = M3.

//     let count = &mut 0;
//     let x = &generateVarFromCount(count, VarType::Node);
//     let y = &generateVarFromCount(count, VarType::Int);

//     let a = generateVarFromCount(count, VarType::Int);
//     let l = generateVarFromCount(count, VarType::Node);
//     let r = generateVarFromCount(count, VarType::Node);
//     let m1 = generateVarFromCount(count, VarType::Int);
//     let m2 = generateVarFromCount(count, VarType::Int);
//     let m3 = generateVarFromCount(count, VarType::Int);

//     let syntax = format!("(pred <{x} {y}>)");

//     // min-leaf(X,Y) <- X=leaf, Y=0
//     let cond1 = format!("(and <(eq {y} 0) (eq {x} (leaf))>)");
//     let chc1 = format!("(new {syntax} {cond1} <>)");

//     let res1 = ematchQueryall(&eg, &Pattern::parse(&chc1).unwrap());
//     assert!(res1.len() > 0);

//     // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), M1 < M2, M3 = M1.
//     let cond2 = format!(
//         "(and <(eq {x} (binode {a} {l} {r})) (eq {y} (+ {m3} 1)) (lt {m1} {m2}) (eq {m3} {m1})>)"
//     );
//     let chc2 = format!(
//         "(new {syntax} {cond2} <{} {}>)",
//         minLeafDummy(&l, &m1),
//         minLeafDummy(&r, &m2),
//     );
//     let res2 = ematchQueryall(&eg, &Pattern::parse(&chc2).unwrap());
//     assert!(res2.len() > 0);

//     // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), M1 >= M2, M2 = M3.
//     let cond3 = format!(
//         "(and <(eq {x} (binode {a} {l} {r})) (eq {y} (+ {m3} 1)) (geq {m1} {m2}) (eq {m2} {m3})>)"
//     );
//     let resCond3 = ematchQueryall(eg, &Pattern::parse(&cond3).unwrap());
//     assert!(resCond3.len() > 0);

//     let chc3 = format!(
//         "(new {syntax} {cond3} <{} {}>)",
//         minLeafDummy(&l, &m1),
//         minLeafDummy(&r, &m2),
//     );
//     let res3 = ematchQueryall(&eg, &Pattern::parse(&chc3).unwrap());
//     assert!(res3.len() > 0);

//     let unfold = format!("(compose <{chc1} {chc2} {chc3}>)");
//     let res = ematchQueryall(&eg, &Pattern::parse(&unfold).unwrap());
//     assert!(res.len() > 0);
//     assert!(res[0].1 == id(&minLeafDummy(x, y), eg).id);
// }
