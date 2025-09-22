#![allow(unused)]
#![allow(non_snake_case)]

use crate::*;
use slotted_egraphs::*;

define_language! {
    pub enum CHC {
        Var(Slot) = "var",
        And(Vec<AppliedId>) = "and",
    }
    // p <- q, r
}

pub fn get_all_rewrites() -> Vec<Rewrite<CHC>> {
    vec![and_assoc(), and_comm(), and_3()]
}

fn and_assoc() -> Rewrite<CHC> {
    let pat = "(and <?1 (and <?2 ?3>)>)";
    let outpat = "(and <(and <?1 ?2>) ?3>)";
    Rewrite::new("and-assoc", pat, outpat)
}

fn and_comm() -> Rewrite<CHC> {
    let pat = "(and <?a ?b>)";
    let outpat = "(and <?b ?a>)";
    Rewrite::new("and-comm", pat, outpat)
}

fn and_3() -> Rewrite<CHC> {
    let pat = "(and <?a (and <?b ?c>)>)";
    let outpat = "(and <?a ?b ?c>)";
    Rewrite::new("and-3", pat, outpat)
}

#[test]
fn and() {
    let x = "$0";
    let y = "$1";
    let z = "$2";

    let a = &format!("(and <(and <(var {x}) (var {y})>) (var {z})>)");
    let b = &format!("(and <(var {x}) (var {y}) (var {z})>)");
    assert_reaches(a, b, &get_all_rewrites()[..], 10);
}
