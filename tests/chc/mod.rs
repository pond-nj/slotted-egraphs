#![allow(unused)]
#![allow(non_snake_case)]

use crate::*;
use env_logger::Builder;
use log::{debug, LevelFilter};
use slotted_egraphs::*;
use std::io::Write;
use std::vec;
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

fn unfold() -> Rewrite<CHC> {
    let pat = Pattern::parse("(compose <(new ?s (true) <(compose <*>) *>) *>)").unwrap();
    // let pat = Pattern::parse("(test1 (test2 ?s (true) (test1 ?a)))").unwrap();
    debug!("pat after parse = {pat:#?}");
    let rt: RewriteT<CHC> = RewriteT {
        searcher: Box::new(|_| ()),
        applier: Box::new(move |(), eg| {
            let result = ematch_all(eg, &pat);
            debug!("eg = {eg:#?}");
            debug!("pat = {pat:#?}");
            for subst in result {
                debug!("subst = {subst:#?}");
                // TODO(Pond): Check if star ordering is BFS or DFS.
                // TODO(Pond): implement rewriting
            }
        }),
    };
    rt.into()

    // let rt: RewriteT<CHC> = RewriteT {
    //     searcher: Box::new(|_| ()),
    //     applier: Box::new(move |(), eg| {
    //         for subst in ematch_all(eg, &pat) {
    //             if eg
    //                 .enodes_applied(&subst["c"])
    //                 .iter()
    //                 .any(|n| matches!(n, Rise::Symbol(_) | Rise::Number(_)))
    //             {
    //                 let orig = pattern_subst(eg, &pat, &subst);
    //                 eg.union_justified(&orig, &subst["c"], Some("let-const".to_string()));
    //             }
    //         }
    //     }),
    // };
    // rt.into()
}

fn get_all_rewrites() -> Vec<Rewrite<CHC>> {
    vec![unfold()]
}

#[test]
fn tst1() {
    initLogger();
    let x = "$0";
    let y = "$1";

    let r1_syntax = &format!("(pred R1 <{x}>)");
    let r1_chc1 = &format!("(new {r1_syntax} (true) <>)");
    let r1_compose = &format!("(compose <{r1_chc1}>)");

    let r2_syntax = &format!("(pred R2 <{y}>)");
    let r2_chc1 = &format!("(new {r2_syntax} (true) <>)");
    let r2_compose = &format!("(compose <{r2_chc1}>)");

    let q_syntax = &format!("(pred Q <{x} {y}>)");
    let q_chc1 = &format!("(new {q_syntax} (true) <{r1_compose} {r2_compose}>)");
    let q_compose = &format!("(compose <{q_chc1}>)");

    let p_syntax = &format!("(pred P <{x} {y}>)");
    let p_chc1 = &format!("(new {p_syntax} (true) <{q_compose}>)");
    let p_compose = &format!("(compose <{p_chc1}>)");

    println!("p_compose = {p_compose}");

    let mut eg = EGraph::<CHC>::default();
    id(&p_compose, &mut eg);

    println!("eg = {eg:?}");

    let mut runner: Runner<CHC> = Runner::default().with_egraph(eg).with_iter_limit(60);
    let report = runner.run(&get_all_rewrites());

    println!("report = {report:?}");
}
