#![allow(unused)]
#![allow(non_snake_case)]

use env_logger::Builder;

use std::env;

use crate::*;
use slotted_egraphs::*;

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
