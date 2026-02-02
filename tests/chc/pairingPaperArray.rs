use std::time::Duration;

use super::*;

const ITER_LIMIT: usize = 3;
const TIME_LIMIT_SECS: u64 = 300;
const DO_CONST_REWRITE: bool = true;
const DO_FOLDING: bool = true;

#[test]
fn mainTest() {
    let mut eg = CHCEGraph::default();
    growEGraph("tests/chc/input/pairing_paper_array.txt", &mut eg);

    println!("Egraph before");
    dumpCHCEGraph(&eg);

    let mut runner: CHCRunner = Runner::default()
        .with_egraph(eg)
        .with_iter_limit(ITER_LIMIT)
        .with_time_limit(Duration::from_secs(TIME_LIMIT_SECS));
    let (report, t): (Report, _) = time(|| {
        runner.run(&mut getAllRewrites(
            RewriteList::default(),
            DO_CONST_REWRITE,
            DO_FOLDING,
        ))
    });
    println!("use time {t:?}");
    println!("report {report:?}");

    println!("Egraph after");
    dumpCHCEGraph(&runner.egraph);
}
