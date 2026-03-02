use std::time::Duration;

use log::{info, logger};

use super::*;

const ITER_LIMIT: usize = 3;
const TIME_LIMIT_SECS: u64 = 300;
const DO_CONST_REWRITE: bool = true;

#[test]
fn mainTest() {
    initLogger();
    let mut eg = CHCEGraph::default();
    growEGraph("tests/chc/cases/synchronized_chc.txt", &mut eg);
    eg.rebuild();

    info!("Egraph before");
    dumpCHCEGraph(&eg);

    let mut runner: CHCRunner = Runner::default()
        .with_egraph(eg)
        .with_iter_limit(ITER_LIMIT)
        .with_time_limit(Duration::from_secs(TIME_LIMIT_SECS));
    // let (report, t): (Report, _) = time(|| {
    //     runner.run(&mut getAllRewrites(
    //         RewriteList::default(),
    //         RewriteOption {
    //             doConstraintRewrite: DO_CONST_REWRITE,
    //             doFolding: true,
    //             doADTDefine: false,
    //             doPairingDefine: true,
    //         },
    //     ))
    // });
    // info!("use time {t:?}");
    // info!("report {report:?}");

    info!("Egraph after");
    dumpCHCEGraph(&runner.egraph);

    // checkGraphExists("tests/chc/cases/synchronized_chc_out3.txt", &runner.egraph);

    let query = "(new (pred <>) (and <(gt (intType $x7) (intType $x8)) (gt (intType $x8) (intType $x9))>) <?y ?z ?x>)";

    let expectedExpr = format!("(compose <{query}>)",);

    let res1: Vec<(Subst, Id)> =
        ematchQueryall(&runner.egraph, &Pattern::parse(&expectedExpr).unwrap());
    assert!(res1.len() > 0);
    println!("res1: {res1:#?}");

    let query = format!("(new (pred <>) (and <(gt (intType $x7) (intType $x8)) (gt (intType $x8) (intType $x9))>) <?y ?z {}>)", "(compose <(new (pred <(intType $x9)>) (and <(eq (intType $x5) 0) (eq (intType $x5) (intType $x9))>) <>)>)");

    let expectedExpr = format!("(compose <{query}>)",);

    let res: Vec<(Subst, Id)> =
        ematchQueryall(&runner.egraph, &Pattern::parse(&expectedExpr).unwrap());
    assert!(res.len() > 0);
    println!("res: {res:?}");

    // let children = "<(compose <(new (pred <(intType $new0)>) (and <(eq (intType $x1) 0) (eq (intType $x1) (intType $new0))>) <>) (new (pred <(intType $new0)>) (and <(eq (intType $x2) (add (intType $x1) 1)) (eq (intType $x2) (intType $new0))>) <?p>)>) (compose <(new (pred <(intType $new0)>) (and <(eq (intType $x3) 0) (eq (intType $x3) (intType $new0))>) <>) (new (pred <(intType $new0)>) (and <(eq (intType $x4) (add (intType $x3) 2)) (eq (intType $x4) (intType $new0))>) <?q>)>) (compose <(new (pred <(intType $new0)>) (and <(eq (intType $x5) 0) (eq (intType $x5) (intType $new0))>) <>)>)>)>";
}
