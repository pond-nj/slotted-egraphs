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
        // PredSyntax(AppliedId, Vec<AppliedId>) = "pred",
        PredSyntax(Vec<AppliedId>) = "pred",
        New(AppliedId, AppliedId, Vec<AppliedIdOrStar>) = "new",
        Compose(Vec<AppliedIdOrStar>) = "compose",
        True() = "true",
        // PredName(String),
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

// TODO: remove syntax enode -> where to put this instead?
// even if we remove syntax from here, we still have to maintain the var some where.
// maybe just remove the predname?, no need to remove all syntax
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

fn pUnfoldedCHC(x: &str, y: &str) -> String {
    let p_syntax = &format!("(pred <{x} {y}>)");
    let p_chc2 = &format!("(new {p_syntax} (true) <>)");
    let unfolded_p_chc1 = &format!(
        "(new {p_syntax} (true) <{} {} {}>)",
        r1CHC(x, y),
        r2CHC(x, y),
        sCHC(x, y)
    );
    format!("(compose <{unfolded_p_chc1} {p_chc2}>)")
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
    debug!("report = {report:?}");
    debug!("eg after rewrite = {:?}", runner.egraph);

    let result = ematch_all(
        &runner.egraph,
        &Pattern::parse(&pUnfoldedCHC("?a", "?b")).unwrap(),
    );
    debug!("match unfold result1 = {result:#?}");
}
