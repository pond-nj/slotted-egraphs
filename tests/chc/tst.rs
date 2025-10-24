use super::*;

use log::debug;

fn r1CHC(x: &str, y: &str) -> String {
    let r1_syntax = &format!("(pred <{x}>)");
    let r1_chc1 = &format!("(new {r1_syntax} (true) <>)");
    format!("(compose <{r1_chc1}>)")
}

fn r2CHC(x: &str, y: &str) -> String {
    let r2_syntax = &format!("(pred <{y}>)");
    let r2_chc1 = &format!("(new {r2_syntax} (true) <>)");
    format!("(compose <{r2_chc1}>)")
}

fn qCHC(x: &str, y: &str) -> String {
    let q_syntax = &format!("(pred <{x} {y}>)");
    let q_chc1 = &format!("(new {q_syntax} (true) <{} {}>)", r1CHC(x, y), r2CHC(x, y));
    format!("(compose <{q_chc1}>)")
}

fn sCHC(x: &str, y: &str) -> String {
    let s_syntax = &format!("(pred <{x}>)");
    let s_chc1 = &format!("(new {s_syntax} (true) <>)");
    format!("(compose <{s_chc1}>)")
}

fn pCHC(x: &str, y: &str) -> String {
    let p_syntax = &format!("(pred <{x} {y}>)");
    // P(x, y) <- Q(x, y), S(x).
    let p_chc1 = &format!("(new {p_syntax} (true) <{} {}>)", qCHC(x, y), sCHC(x, y));
    // P(x, y) <- .
    let p_chc2 = &format!("(new {p_syntax} (true) <>)");
    format!("(compose <{p_chc1} {p_chc2}>)")
}

#[test]
fn tst1() {
    initLogger();
    let pCompose = pCHC("(var $0)", "(var $1)");
    debug!("p_compose = {}", pCompose);

    let mut eg = CHCEGraph::default();
    id(&pCompose, &mut eg);

    let mut runner: CHCRunner = Runner::default().with_egraph(eg).with_iter_limit(60);
    let report = runner.run(&getAllRewrites());

    let x = "?a";
    let y = "?b";
    let p_syntax = &format!("(pred <{x} {y}>)");
    let p_chc2 = &format!("(new {p_syntax} (true) <>)");
    let children = vec![r1CHC(x, y), r2CHC(x, y), sCHC(x, y)];

    let permutation = permute(&children);
    assert!(permutation.len() == 6);
    for p in permutation {
        let unfolded_p_chc1 = &format!("(new {p_syntax} (true) <{} {} {}>)", p[0], p[1], p[2]);
        let newRoot = format!("(compose <{unfolded_p_chc1} {p_chc2}>)");
        let resultLen = ematch_all(&runner.egraph, &Pattern::parse(&newRoot).unwrap()).len();
        assert!(resultLen > 0);
    }
}

fn minDummy(x: &str, y: &str, z: &str) -> String {
    let syntax = format!("(pred <{x} {y}>)");
    format!("(init min {syntax})")
}

fn minCHC(x: &str, y: &str, z: &str) -> String {
    let syntax = format!("(pred <{x} {y} {z}>)");
    // min(X,Y,Z) <- X< Y, Z=X
    let cond1 = format!("(and <(lt {x} {y}) (eq {z} {x})>)");
    let chc1 = format!("(new {syntax} {cond1} <>)");

    // min(X,Y,Z) <- X >= Y, Z=Y
    let cond2 = format!("(and <(geq {x} {y}) (eq {z} {y})>)");
    let chc2 = format!("(new {syntax} {cond2} <>)");

    format!("(compose <{chc1} {chc2}>)")
}

fn minLeafDummy(x: &str, y: &str) -> String {
    let syntax = format!("(pred <{x} {y}>)");
    format!("(init minLeaf {syntax})")
}

fn minLeafCHC(x: &str, y: &str, count: &mut u32) -> String {
    let a = generateIntVar(count);
    let l = generateNodeVar(count);
    let r = generateNodeVar(count);
    let m1 = generateIntVar(count);
    let m2 = generateIntVar(count);
    let m3 = generateIntVar(count);

    let syntax = format!("(pred <{x} {y}>)");

    // min-leaf(X,Y) <- X=leaf, Y=0
    let cond1 = format!("(and <(eq {y} 0) (eq {x} (leaf))>)");
    let chc1 = format!("(new {syntax} {cond1} <>)");

    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)
    let cond2 = format!("(and <(eq {x} (binode {a} {l} {r})) (eq {y} (+ {m3} 1))>)");
    let chc2 = format!(
        "(new {syntax} {cond2} <{} {} {}>)",
        minLeafDummy(&l, &m1),
        minLeafDummy(&r, &m2),
        minCHC(&m1, &m2, &m3)
    );

    format!("(compose <{chc1} {chc2}>)")
}

fn leafDropDummy(x: &str, y: &str, z: &str) -> String {
    let syntax = format!("(pred <{x} {y} {z}>)");
    format!("(init leafDrop {syntax})")
}

fn leafDropCHC(x: &str, y: &str, z: &str, count: &mut u32) -> String {
    let syntax = format!("(pred <{x} {y} {z}>)");

    // left-drop(x,y,z) ← y=leaf, z=leaf
    let cond1 = format!("(and <(eq {y} (leaf)) (eq {z} (leaf))>)");
    let chc1 = format!("(new {syntax} {cond1} <>)");

    let l = generateNodeVar(count);
    let r = generateNodeVar(count);
    let a = generateIntVar(count);
    // left-drop(x, y ,z) ← x ≤0, y = node(a,L,R), z = node(a,L,R)
    let cond2 =
        format!("(and <(leq {x} 0) (eq {y} (binode {a} {l} {r})) (eq {z} (binode {a} {l} {r}))>)");
    let chc2 = format!("(new {syntax} {cond2} <>)");

    let l1 = generateNodeVar(count);
    let r1 = generateNodeVar(count);
    let a1 = generateIntVar(count);
    let n1 = generateIntVar(count);

    // left-drop(x,y,z) ← y= node(a,L,R), x ≥1,N1=x−1, left-drop(N1,L,z)
    let cond3 = format!("(and <(eq {y} (binode {a1} {l1} {r1})) (geq {x} 1) (eq {n1} (- {x} 1))>)");
    let chc3 = format!("(new {syntax} {cond3} <{}>)", leafDropDummy(x, y, z));

    format!("(compose <{chc1} {chc2} {chc3}>)")
}

fn rootDummy(n: &str, t: &str, u: &str, m: &str, k: &str) -> String {
    let syntax = format!("(pred <{n} {t} {u} {m} {k}>)");
    format!("(init root {syntax})")
}

fn addPredName(id: Id, predName: String, eg: &mut CHCEGraph) {
    let data = eg.analysis_data_mut(id);
    data.predNames.insert(predName);
}

#[test]
fn tst2() {
    // TODO: how to determine slot type?
    initLogger();
    let mut count = 0;
    let n = &generateIntVar(&mut count);
    let t = &generateNodeVar(&mut count);
    let u = &generateNodeVar(&mut count);
    let m = &generateIntVar(&mut count);
    let k = &generateIntVar(&mut count);

    //  false ← N≥0,M+N<K, left-drop(N,T,U), min-leaf(U,M), min-leaf(T,K)
    let syntax = "(pred <>)";
    let cond = format!("(and <(geq {n} 0) (lt (+ {m} {n}) {k})>)");
    let rootCHC: String = format!(
        "(new {syntax} {cond} <{} {} {}>)",
        leafDropDummy(n, t, u),
        minLeafDummy(u, m),
        minLeafDummy(t, k)
    );
    let composeRoot = format!("(compose <{rootCHC}>)");

    let mut eg = CHCEGraph::default();

    // TODO: must add dummy first for data
    let rootDummyId = id(&rootDummy(n, t, u, m, k), &mut eg);
    let rootId = id(&composeRoot, &mut eg);
    // addPredName(rootId.id, "root".to_string(), &mut eg);
    eg.union(&rootId, &rootDummyId);

    let x = &generateIntVar(&mut count);
    let y = &generateIntVar(&mut count);
    let z = &generateIntVar(&mut count);

    let minDummyId = id(&minDummy(x, y, z), &mut eg);
    let minId = id(&minCHC(x, y, z), &mut eg);
    eg.union(&minDummyId, &minId);

    let x = &generateIntVar(&mut count);
    let y = &generateNodeVar(&mut count);
    let z = &generateNodeVar(&mut count);

    let leafDropDummyId = id(&leafDropDummy(x, y, z), &mut eg);
    let leafDropId = id(&leafDropCHC(x, y, z, &mut count), &mut eg);
    eg.union(&leafDropDummyId, &leafDropId);

    let x = &generateNodeVar(&mut count);
    let y = &generateIntVar(&mut count);

    let minLeafDummyId = id(&minLeafDummy(x, y), &mut eg);
    let minLeafId = id(&minLeafCHC(x, y, &mut count), &mut eg);
    eg.union(&minLeafDummyId, &minLeafId);

    debug!("egraph after");
    dumpCHCEgraph(&eg);

    // TODO: add data to eclass and print data when print egraph
}

#[test]
fn tst3() {
    // TODO: how to determine slot type?
    initLogger();

    let mut eg = CHCEGraph::default();
    let mut count = 0;
    let x = generateIntVar(&mut count);
    let y = generateIntVar(&mut count);
    let minLeaf = minLeafCHC(&x, &y, &mut count);
    id(&minLeaf, &mut eg);

    dumpCHCEgraph(&eg);

    // TODO: add data to eclass and print data when print egraph
}
