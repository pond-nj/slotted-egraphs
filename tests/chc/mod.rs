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

// TODO(Pond): Star should only be allowed inside a vector(dynamic length)
define_language! {
    pub enum And {
        Var(Slot) = "var",
        And(Vec<AppliedIdOrStar>) = "and",
    }
    // p <- q, r
}

pub fn get_all_and_rewrites() -> Vec<Rewrite<And>> {
    // vec![and_assoc(), and_comm(), and_3()]
    vec![and_tmp()]
}

fn and_assoc() -> Rewrite<And> {
    let pat = "(and <?1 (and <?2 ?3>)>)";
    let outpat = "(and <(and <?1 ?2>) ?3>)";
    Rewrite::new("and-assoc", pat, outpat)
}

fn and_comm() -> Rewrite<And> {
    let pat = "(and <?a ?b>)";
    let outpat = "(and <?b ?a>)";
    Rewrite::new("and-comm", pat, outpat)
}

fn and_3() -> Rewrite<And> {
    let pat = "(and <?a (and <?b ?c>)>)";
    let outpat = "(and <?a ?b ?c>)";
    Rewrite::new("and-3", pat, outpat)
}

fn and_tmp() -> Rewrite<And> {
    // let pat = "(and <?a *>)";
    // TODO(Pond): (and <?a *> ?b)
    let pat = "(and <(and <?b *>) *>)";
    let outpat = "(and <?a>)";
    Rewrite::new("and-tmp", pat, outpat)
}

// #[test]
fn and() {
    env_logger::builder()
        .format_timestamp(None)
        .format_level(false)
        .format_target(true)
        .filter_level(LevelFilter::Debug)
        .init();

    let x = "$0";
    let y = "$1";
    let z = "$2";
    let w = "$3";

    let a = &format!("(and <(and <(var {x}) (var {y})>) (and <(var {z}) (var {w})>)>)");
    let b = &format!("(and <(var {x}) (var {y}) (var {z})>)");
    assert_reaches(a, b, &get_all_and_rewrites()[..], 10);
}

define_language! {
    // TODO(Pond): now children can only have max one vector
    pub enum CHC {
        Var(Slot) = "var",
        PredSyntax(AppliedId, Vec<Slot>) = "pred", //(pred P <$1>)
        New(AppliedId, AppliedId, Vec<AppliedIdOrStar>) = "new", // (new PredSyntax Constraint <Body>)
        Compose(Vec<AppliedIdOrStar>) = "compose",
        // Test1(AppliedId) = "test1",
        // Test2(AppliedId, AppliedId, AppliedId) = "test2",
        True() = "true",
        PredName(String),
    }
}

// TODO(Pond): next, we need testing here
fn unfold() -> Rewrite<CHC> {
    let rootPatRaw =
        Pattern::parse("(compose <(new ?syntax1 (true) <(compose <*1>) *2>) *3>)").unwrap();
    let rootPat: Rc<Pattern<CHC>> = Rc::new(rootPatRaw);
    let rootPat2 = Rc::clone(&rootPat);

    let searcher = Box::new(move |eg: &EGraph<CHC>| -> Vec<Subst> { ematch_all(eg, &rootPat) });
    let applier = Box::new(
        // (compose <[(new ?syntax2 (true) <*4>) \dot (#matches of *1)] *3>)
        move |substs: Vec<Subst>, eg: &mut EGraph<CHC>| {
            for subst in substs {
                let mut star1Max = 0;
                while subst.contains_key(&starPVar(1, star1Max)) {
                    star1Max += 1;
                }

                let mut matches: Vec<Vec<AppliedId>> = vec![];
                // match in star1 Eclass
                for star1Count in 0..star1Max {
                    let subPat = Pattern::parse("(new ?syntax2 (true) <*4>)").unwrap();
                    let result: Vec<Subst> =
                        ematchAllInEclass(eg, &subPat, subst[&starPVar(1, star1Count)].id);
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

#[test]
fn tst1() {
    initLogger();
    let x = "$0";
    let y = "$1";

    // r1(x) <- .
    let r1_syntax = &format!("(pred R1 <{x}>)");
    let r1_chc1 = &format!("(new {r1_syntax} (true) <>)");
    let r1_compose = &format!("(compose <{r1_chc1}>)");

    // r2(y) <- .
    let r2_syntax = &format!("(pred R2 <{y}>)");
    let r2_chc1 = &format!("(new {r2_syntax} (true) <>)");
    let r2_compose = &format!("(compose <{r2_chc1}>)");

    // Q(x, y) <- r1(x), r2(y).
    let q_syntax = &format!("(pred Q <{x} {y}>)");
    let q_chc1 = &format!("(new {q_syntax} (true) <{r1_compose} {r2_compose}>)");
    let q_compose = &format!("(compose <{q_chc1}>)");

    // S(x) <- .
    let s_syntax = &format!("(pred S <{x}>)");
    let s_chc1 = &format!("(new {s_syntax} (true) <>)");
    let s_compose = &format!("(compose <{s_chc1}>)");

    let p_syntax = &format!("(pred P <{x} {y}>)");
    // P(x, y) <- Q(x, y), S(x).
    let p_chc1 = &format!("(new {p_syntax} (true) <{q_compose} {s_compose}>)");
    // P(x, y) <- .
    let p_chc2 = &format!("(new {p_syntax} (true) <>)");
    let p_compose = &format!("(compose <{p_chc1} {p_chc2}>)");

    debug!("p_compose = {p_compose}");

    let mut eg = EGraph::<CHC>::default();
    id(&p_compose, &mut eg);

    let mut runner: Runner<CHC> = Runner::default().with_egraph(eg).with_iter_limit(60);
    let report = runner.run(&get_all_rewrites());
    debug!("report = {report:?}");
    debug!("eg after rewrite = {:?}", runner.egraph);

    // unfold result
    // P(x, y) <- r1(x), r2(y), S(x).
    // P(x, y) <- .
    let unfolded_p_chc1 =
        &format!("(new {p_syntax} (true) <{r1_compose} {r2_compose} {s_compose}>)");
    let unfolded_p_compose = &format!("(compose <{unfolded_p_chc1} {p_chc2}>)");

    let result = ematch_all(&runner.egraph, &Pattern::parse(unfolded_p_compose).unwrap());
    debug!("match unfold result1 = {result:?}");
}
