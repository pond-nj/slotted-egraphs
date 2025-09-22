#![allow(unused)]
#![allow(non_snake_case)]

use crate::*;
use slotted_egraphs::*;

define_language! {
    pub enum CHC {
        Var(Slot) = "var",
        Pred(AppliedId, Vec<Slot>) = "pred", //(pred P <$1>)
        New(AppliedId, AppliedId, Vec<AppliedId>) = "new", // (new Pred Constraint <Body>)
        Compose(Vec<AppliedId>) = "compose",
        True() = "true",
        False() = "false",
        PredName(String),
    }
}

pub fn get_all_rewrites() -> Vec<Rewrite<CHC>> {
    vec![unfold()]
}

fn unfold() -> Rewrite<CHC> {
    let pat = "(and <?1 (and <?2 ?3>)>)";
    let outpat = "(and <(and <?1 ?2>) ?3>)";
    Rewrite::new("unfold", pat, outpat)
}

#[test]
fn tst1() {
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

    let eg = &mut EGraph::<CHC>::default();
    id(&p_compose, eg);

    eg.dump();
    // assert_reaches(a, b, &get_all_rewrites()[..], 10);
}
