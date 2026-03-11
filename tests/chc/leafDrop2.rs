// https://arxiv.org/pdf/1804.09007

use std::time::Duration;

use log::{info, logger};

use super::*;

const ITER_LIMIT: usize = 3;
const TIME_LIMIT_SECS: u64 = 300;

#[test]
fn mainTest() {
    initLogger();
    let mut eg = CHCEGraph::default();
    growEGraph("tests/chc/cases/leaf_drop.txt", &mut eg);
    eg.rebuild();

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
                doADTDefine: true,
                doPairingDefine: true,
            },
        ))
    });
    info!("use time {t:?}");
    info!("report {report:?}");

    info!("Egraph after");
    dumpCHCEGraph(&runner.egraph);

    checkCHCExists("tests/chc/cases/leaf_drop_out.txt", &runner.egraph);
}
