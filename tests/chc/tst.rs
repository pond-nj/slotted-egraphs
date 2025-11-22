use std::cell::RefCell;

use super::*;

use log::debug;

fn r1Dummy(x: &str, y: &str) -> String {
    let r1_syntax = &format!("(pred <{x}>)");
    format!("(init r1 {r1_syntax})")
}

fn r1CHC(x: &str, y: &str) -> String {
    let r1_syntax = &format!("(pred <{x}>)");
    let r1_chc1 = &format!("(new {r1_syntax} (true) <>)");
    format!("(compose <{r1_chc1}>)")
}

fn r2Dummy(x: &str, y: &str) -> String {
    let r2_syntax = &format!("(pred <{y}>)");
    format!("(init r2 {r2_syntax})")
}

fn r2CHC(x: &str, y: &str) -> String {
    let r2_syntax = &format!("(pred <{y}>)");
    let r2_chc1 = &format!("(new {r2_syntax} (true) <>)");
    format!("(compose <{r2_chc1}>)")
}

fn qDummy(x: &str, y: &str) -> String {
    let q_syntax = &format!("(pred <{x} {y}>)");
    format!("(init q {q_syntax})")
}

fn qCHC(x: &str, y: &str) -> String {
    let q_syntax = &format!("(pred <{x} {y}>)");
    let q_chc1 = &format!(
        "(new {q_syntax} (true) <{} {}>)",
        r1Dummy(x, y),
        r2Dummy(x, y)
    );
    format!("(compose <{q_chc1}>)")
}

fn sDummy(x: &str, y: &str) -> String {
    let s_syntax = &format!("(pred <{x}>)");
    format!("(init s {s_syntax})")
}

fn sCHC(x: &str, y: &str) -> String {
    let s_syntax = &format!("(pred <{x}>)");
    let s_chc1 = &format!("(new {s_syntax} (true) <>)");
    format!("(compose <{s_chc1}>)")
}

fn pCHC(x: &str, y: &str) -> String {
    let p_syntax = &format!("(pred <{x} {y}>)");
    // P(x, y) <- Q(x, y), S(x).
    let p_chc1 = &format!(
        "(new {p_syntax} (true) <{} {}>)",
        qDummy(x, y),
        sDummy(x, y)
    );
    // P(x, y) <- .
    let p_chc2 = &format!("(new {p_syntax} (true) <>)");
    format!("(compose <{p_chc1} {p_chc2}>)")
}

fn pDummy(x: &str, y: &str) -> String {
    let p_syntax = &format!("(pred <{x} {y}>)");
    format!("(init p {p_syntax})")
}

#[test]
fn tst1() {
    initLogger();
    let mut eg = CHCEGraph::default();
    let mut unfoldList = Rc::new(RefCell::new(vec![]));
    let mut constrRewriteList = Rc::new(RefCell::new(vec![]));
    let x = "(var $0)";
    let y = "(var $1)";
    let pCompose = pCHC(x, y);

    let chcPair = [
        (qCHC(x, y), qDummy(x, y)),
        (r1CHC(x, y), r1Dummy(x, y)),
        (r2CHC(x, y), r2Dummy(x, y)),
        (sCHC(x, y), sDummy(x, y)),
        (pCHC(x, y), pDummy(x, y)),
    ];

    for (c, cDummy) in chcPair {
        let cId = id(&c, &mut eg);
        let cDummyId = id(&cDummy, &mut eg);
        eg.union(&cId, &cDummyId);
    }

    let rootId = id(&pCHC(x, y), &mut eg);

    let mut runner: CHCRunner = Runner::default().with_egraph(eg).with_iter_limit(5);
    let report = runner.run(&mut getAllRewrites(&unfoldList, &constrRewriteList));
    debug!("report {report:?}");
    debug!("egraph after");
    dumpCHCEGraph(&runner.egraph);

    // find
    // P(x, y) <- .
    // P(x, y) <- r1(x), r2(y), S(x).

    let x = "?a";
    let y = "?b";
    let p_syntax = &format!("(pred <{x} {y}>)");
    let p_chc2 = &format!("(new {p_syntax} (true) <>)");
    let children = vec![r1CHC(x, y), r2CHC(x, y), sCHC(x, y)];

    let permutation = permute(&children);
    let mut found = false;

    debug!("rootId {rootId:?}");

    let unfolded_p_chc1 = &format!(
        "(new {p_syntax} (and <>) <{} {} {}>)",
        r1Dummy(x, y),
        r2Dummy(x, y),
        sDummy(x, y)
    );
    let newRoot = format!("(compose <{p_chc2} {unfolded_p_chc1}>)");
    let result = ematchQueryall(&runner.egraph, &Pattern::parse(&newRoot).unwrap());
    assert!(result.len() > 0);
    assert!(result[1].1 == rootId.id);

    // find
    // P(x, y).
    // P(x, y).
    let x = "?a";
    let y = "?b";
    let p_syntax = &format!("(pred <{x} {y}>)");
    let p_chc2 = &format!("(new {p_syntax} (true) <>)");
    let unfoldBoth = format!("(compose <{p_chc2} {p_chc2}>)");
    let result = ematch_all(&runner.egraph, &Pattern::parse(&unfoldBoth).unwrap());
    assert!(result.len() > 0);
    assert!(result.first().unwrap().1 == rootId.id);
}
