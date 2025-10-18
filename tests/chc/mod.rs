#![allow(unused)]
#![allow(non_snake_case)]

use crate::*;
use env_logger::Builder;
use log::{debug, LevelFilter};
use slotted_egraphs::*;
use std::collections::BTreeSet;
use std::rc::Rc;
use std::vec;
use std::{default, io::Write};
use tracing_subscriber::{fmt, prelude::*};

define_language! {
    // TODO(Pond): now children can only have max one vector
    pub enum CHC {
        Var(Slot) = "var",

        PredSyntax(Vec<AppliedId>) = "pred",
        New(AppliedId, AppliedId, Vec<AppliedIdOrStar>) = "new",
        Compose(Vec<AppliedIdOrStar>) = "compose",
        True() = "true",

        // node(x, l, r) has subtree l and r and element x at this node
        Node(AppliedId, AppliedId, AppliedId) = "node",
        Leaf() = "leaf",

        // Boolean
        And(Vec<AppliedId>) = "and",

        // Arithmetic
        Geq(AppliedId, AppliedId) = "geq",
        Leq(AppliedId, AppliedId) = "leq",
        Less(AppliedId, AppliedId) = "lt",
        Greater(AppliedId, AppliedId) = "gt",
        Eq(AppliedId, AppliedId) = "eq",
        Add(AppliedId, AppliedId) = "+",
        Minus(AppliedId, AppliedId) = "-",

        Number(u32),

        // (init predName syntax)
        // use to create empty compose eclass for recursive definition
        Init(AppliedId, AppliedId) = "init",
        PredName(String),
    }
}

fn unfold() -> Rewrite<CHC> {
    let rootPatRaw =
        Pattern::parse("(compose <(new ?syntax1 (true) <(compose <*1>) *2>) *3>)").unwrap();
    let rootPat: Rc<Pattern<CHC>> = Rc::new(rootPatRaw);
    let rootPat2 = Rc::clone(&rootPat);

    let searcher = Box::new(move |eg: &EGraph<CHC>| -> Vec<Subst> { ematch_all(eg, &rootPat) });
    let applier = Box::new(
        // (compose <[(new ?syntax2 (true) <*4>) \dot (#matches of *1)] *3>)
        move |substs: Vec<Subst>, eg: &mut EGraph<CHC>| {
            debug!("unfold rule, found {:#?}", substs);
            for subst in substs {
                let star1Max = getMaxStarCount(1, &subst);

                let mut matches: Vec<Vec<AppliedId>> = vec![];
                // match in star1 Eclass
                for star1Count in 0..star1Max {
                    let subPat = Pattern::parse("(new ?syntax2 (true) <*4>)").unwrap();
                    let var = &starPVar(1, star1Count);
                    let result: Vec<Subst> =
                        ematchAllInEclass(eg, &subPat, subst[var].id, &subst[var].m);
                    let mut thisNewIds: Vec<AppliedId> = vec![];

                    let toPat = Pattern::parse(&format!(
                        "(new ?syntax1 (true) <{} *4>)",
                        starPStr(2, &subst)
                    ))
                    .unwrap();

                    for mut r in result {
                        mergeSubst(&mut r, &subst);
                        let newId = pattern_subst(eg, &toPat, &r);
                        thisNewIds.push(newId);
                    }
                    matches.push(thisNewIds);
                }

                let matchesCombination: Vec<Vec<AppliedId>> = combination(matches);
                let newEnode =
                    Pattern::parse(&format!("(compose <{} *4>)", starPStr(3, &subst))).unwrap();
                for m in matchesCombination {
                    // Create a new compose Enode whose children is the vector of AppliedId and union it with the original Compose
                    let mut newSubst = subst.clone();
                    let mut star4Count = 0;
                    for id in m {
                        let key = starPVar(4, star4Count);
                        assert!(!newSubst.contains_key(&key));
                        newSubst.insert(key, id);
                        star4Count += 1;
                    }

                    eg.union_instantiations(
                        &*rootPat2,
                        &newEnode,
                        &newSubst,
                        Some("Unfold".to_string()),
                    );
                }
            }
        },
    );
    RewriteT {
        searcher: searcher,
        applier: applier,
    }
    .into()
}

fn newChildrenPermute() -> Rewrite<CHC> {
    let pat = Pattern::parse("(new ?syntax ?cond <*1>)").unwrap();
    let patClone = pat.clone();
    let searcher = Box::new(move |eg: &EGraph<CHC>| -> Vec<Subst> { ematch_all(eg, &patClone) });
    let applier = Box::new(move |substs: Vec<Subst>, eg: &mut EGraph<CHC>| {
        // TODO: is there a different between using AppliedId and Id
        let mut did = HashSet::<(AppliedId, AppliedId, BTreeSet<AppliedId>)>::default();
        let newPat = Pattern::parse("(new ?syntax ?cond <*2>)").unwrap();
        for subst in substs {
            let mut thisDid = BTreeSet::<AppliedId>::default();
            for (var, id) in subst.iter() {
                thisDid.insert(id.clone());
            }

            let mut this = (subst["syntax"].clone(), subst["cond"].clone(), thisDid);
            if did.contains(&this) {
                continue;
            }

            did.insert(this);

            let ids = starIds(1, &subst);
            let idsPermuts = permute(&ids);
            let mut newSubst = subst.clone();
            for permut in idsPermuts {
                let mut newSubstTmp = newSubst.clone();
                for (i, id) in permut.iter().enumerate() {
                    newSubstTmp.insert(starPVar(2, i.try_into().unwrap()), id.clone());
                }
                eg.union_instantiations(
                    &pat,
                    &newPat,
                    &newSubstTmp,
                    Some("newChildrenPermute".to_string()),
                );
            }
        }
    });
    RewriteT { searcher, applier }.into()
}

fn composeChildrenPermute() -> Rewrite<CHC> {
    let pat = Pattern::parse("(compose <*1>)").unwrap();
    let patClone = pat.clone();
    let searcher = Box::new(move |eg: &EGraph<CHC>| -> Vec<Subst> { ematch_all(eg, &patClone) });
    let applier = Box::new(move |substs: Vec<Subst>, eg: &mut EGraph<CHC>| {
        // TODO: is there a different between using AppliedId and Id
        let mut did = HashSet::<BTreeSet<AppliedId>>::default();
        let newPat = Pattern::parse("(compose <*2>)").unwrap();
        for subst in substs {
            let mut thisDid = BTreeSet::<AppliedId>::default();
            for (var, id) in subst.iter() {
                thisDid.insert(id.clone());
            }

            if did.contains(&thisDid) {
                continue;
            }

            did.insert(thisDid);

            let ids = starIds(1, &subst);
            let idsPermuts = permute(&ids);
            let mut newSubst = subst.clone();
            for permut in idsPermuts {
                let mut newSubstTmp = newSubst.clone();
                for (i, id) in permut.iter().enumerate() {
                    newSubstTmp.insert(starPVar(2, i.try_into().unwrap()), id.clone());
                }
                eg.union_instantiations(
                    &pat,
                    &newPat,
                    &newSubstTmp,
                    Some("composeChildrenPermute".to_string()),
                );
            }
        }
    });
    RewriteT { searcher, applier }.into()
}

// TODO: add rule for rearrangement in compose and new children?
fn get_all_rewrites() -> Vec<Rewrite<CHC>> {
    vec![unfold(), newChildrenPermute(), composeChildrenPermute()]
}

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

    let mut eg = EGraph::<CHC>::default();
    id(&pCompose, &mut eg);

    let mut runner: Runner<CHC> = Runner::default().with_egraph(eg).with_iter_limit(60);
    let report = runner.run(&get_all_rewrites());

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
    let a = generateInternalVar(count);
    let l = generateInternalVar(count);
    let r = generateInternalVar(count);
    let m1 = generateInternalVar(count);
    let m2 = generateInternalVar(count);
    let m3 = generateInternalVar(count);

    let syntax = format!("(pred <{x} {y}>)");

    // min-leaf(X,Y) <- X=leaf, Y=0
    let cond1 = format!("(and <(eq {y} 0) (eq {x} (leaf))>)");
    let chc1 = format!("(new {syntax} {cond1} <>)");

    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)
    let cond2 = format!("(and <(eq {x} (node {a} {l} {r})) (eq {y} (+ {m3} 1))>)");
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

    // todo: will these internal variables appear in the expose api for the eclass?
    // can it not appear?

    let l = generateInternalVar(count);
    let r = generateInternalVar(count);
    let a = generateInternalVar(count);
    // left-drop(x, y ,z) ← x ≤0, y = node(a,L,R), z = node(a,L,R)
    let cond2 =
        format!("(and <(leq {x} 0) (eq {y} (node {a} {l} {r})) (eq {z} (node {a} {l} {r}))>)");
    let chc2 = format!("(new {syntax} {cond2} <>)");

    let l1 = generateInternalVar(count);
    let r1 = generateInternalVar(count);
    let a1 = generateInternalVar(count);
    let n1 = generateInternalVar(count);

    // left-drop(x,y,z) ← y= node(a,L,R), x ≥1,N1=x−1, left-drop(N1,L,z)
    let cond3 = format!("(and <(eq {y} (node {a1} {l1} {r1})) (geq {x} 1) (eq {n1} (- {x} 1))>)");
    let chc3 = format!("(new {syntax} {cond3} <{}>)", leafDropDummy(x, y, z));

    format!("(compose <{chc1} {chc2} {chc3}>)")
}

#[test]
fn tst2() {
    initLogger();
    let mut count = 0;
    let n = generateInternalVar(&mut count);
    let t = generateInternalVar(&mut count);
    let u = generateInternalVar(&mut count);
    let m = generateInternalVar(&mut count);
    let k = generateInternalVar(&mut count);

    //  false ← N≥0,M+N<K, left-drop(N,T,U), min-leaf(U,M), min-leaf(T,K)
    let syntax = "(pred <>)";
    let cond = format!("(and <(geq {n} 0) (lt (+ {m} {n}) {k})>)");
    let rootCHC = format!(
        "(new {syntax} {cond} <{} {} {}>)",
        leafDropDummy(&n, &t, &u),
        minLeafDummy(&u, &m),
        minLeafDummy(&t, &k)
    );
    let composeRoot = "(compose <{rootCHC}>)";

    let mut eg = EGraph::<CHC>::default();
    id(&rootCHC, &mut eg);

    let x = "(var $0)";
    let y = "(var $1)";
    let z = "(var $2)";

    let leafDropDummyId = id(&leafDropDummy(x, y, z), &mut eg);
    let leafDropId = id(&leafDropCHC(x, y, z, &mut count), &mut eg);
    eg.union(&leafDropDummyId, &leafDropId);

    let minLeafDummyId = id(&minLeafDummy(x, y), &mut eg);
    let minLeafId = id(&minLeafCHC(x, y, &mut count), &mut eg);
    eg.union(&minLeafDummyId, &minLeafId);

    debug!("egraph after {}", eg);
}
