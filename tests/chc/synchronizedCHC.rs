use std::time::Duration;

use log::{info, logger};

use super::*;

const ITER_LIMIT: usize = 3;
const TIME_LIMIT_SECS: u64 = 300;

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
    let (report, t): (Report, _) = time(|| {
        runner.run(&mut getAllRewrites(
            RewriteList::default(),
            RewriteOption {
                doConstraintRewrite: true,
                doFolding: true,
                doADTDefine: false,
                doPairingDefine: true,
            },
        ))
    });
    info!("use time {t:?}");
    info!("report {report:?}");

    info!("Egraph after");
    dumpCHCEGraph(&runner.egraph);

    // (compose <
    // (new (pred <(intType $f115) (intType $f116)>) (and <(eq (intType $f115) (0))>) <(composeInit (q) (pred <(intType $f116)>) (false) <>)>)
    // (new (pred <(intType $f115) (intType $f116)>) (and <(eq (intType $f115) (add (intType $f487) (1)))>) <(composeInit (p) (pred <(intType $f487)>) (false) <>) (composeInit (q) (pred <(intType $f116)>) (false) <>)>)>)

    // let expr = "(new (pred <(intType $new0) (intType $new1)>) (and <(eq (intType $a_0) 0) (eq (intType $a_0) (intType $new0)) (eq (intType $b_0) (intType $new1))>) <?q_0>)";

    // // (new (pred <(intType $f473) (intType $f474)>) (and <(eq (intType $f473) (0))>) <(composeInit (q) (pred <(intType $f474)>) (false) <>)>)

    // let res1 = ematchQueryAllInEclass(Id(85), &Pattern::parse(expr).unwrap(), &runner.egraph);
    // println!("res1 {res1:?}");
    // assert!(res1.len() > 0);

    // let expr = "(compose <(new (pred <(intType $new0) (intType $new1)>) (and <(eq (intType $a_0) 0) (eq (intType $a_0) (intType $new0)) (eq (intType $b_0) (intType $new1))>) <?q_0>) (new (pred <(intType $new0) (intType $new1)>) (and <(eq (intType $a_1) (add (intType $x1_1) 1)) (eq (intType $a_1) (intType $new0)) (eq (intType $b_1) (intType $new1))>) <?p_1 ?q_1>)>)";

    // let res = ematchQueryAllInEclass(Id(40), &Pattern::parse(expr).unwrap(), &runner.egraph);
    // println!("res {res:?}");
    // assert!(res.len() > 0);

    checkCHCExists("tests/chc/cases/synchronized_chc_out1.txt", &runner.egraph);
}
