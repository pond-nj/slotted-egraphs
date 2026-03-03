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

    // (new (pred <(intType $f18)>) (and <(eq (intType $f19) (0)) (eq (intType $f19) (intType $f18))>) <>)
    // (new (pred <(intType $f29)>) (and <(eq (intType $f31) (intType $f29)) (eq (intType $f31) (add (intType $f30) (1)))>) <(composeInit (p) (pred <(intType $f30)>) (false) <>)>)
    // let expr = "(compose <
    // (new (pred <(intType $new0)>) (and <(eq (intType $x1) 0) (eq (intType $x1) (intType $new0))>) <>)
    // (new (pred <(intType $new0)>) (and <(eq (intType $x2) (add (intType $x1) 1)) (eq (intType $x2) (intType $new0))>) <?p_1>)>)";

    let expr = "(compose <
    (new (pred <(intType $new0)>) (and <(eq (intType $x1) (0)) (eq (intType $x1) (intType $new0))>) <>) 
    (new (pred <(intType $new0)>) (and <(eq (intType $x2) (intType $new0)) (eq (intType $x2) (add (intType $x3) (1)))>) <?p_1>)>)";

    // (compose <
    // (new (pred <(intType $new0_0)>) (and <(eq (intType $x1_0) 0) (eq (intType $x1_0) (intType $new0_0))>) <>)
    // (new (pred <(intType $new0_1)>) (and <(eq (intType $x2_1) (add (intType $x1_1) 1)) (eq (intType $x2_1) (intType $new0_1))>) <?p_1>)>)

    // let res = ematchQueryall(&runner.egraph, &Pattern::parse(&expr).unwrap());

    let appId = runner.egraph.mk_sem_identity_applied_id(Id(7));
    let result = ematchQueryAllInEclass(
        &Pattern::parse(&expr).unwrap(),
        State::default(),
        appId,
        &runner.egraph,
    );
    let res = result.into_iter().map(final_subst).map(|x| (x, Id(7)));

    assert!(res.len() > 0);

    checkCHCExists("tests/chc/cases/synchronized_chc_out3.txt", &runner.egraph);

    // let children = "<(compose <(new (pred <(intType $new0)>) (and <(eq (intType $x1) 0) (eq (intType $x1) (intType $new0))>) <>) (new (pred <(intType $new0)>) (and <(eq (intType $x2) (add (intType $x1) 1)) (eq (intType $x2) (intType $new0))>) <?p>)>) (compose <(new (pred <(intType $new0)>) (and <(eq (intType $x3) 0) (eq (intType $x3) (intType $new0))>) <>) (new (pred <(intType $new0)>) (and <(eq (intType $x4) (add (intType $x3) 2)) (eq (intType $x4) (intType $new0))>) <?q>)>) (compose <(new (pred <(intType $new0)>) (and <(eq (intType $x5) 0) (eq (intType $x5) (intType $new0))>) <>)>)>)>";
}
