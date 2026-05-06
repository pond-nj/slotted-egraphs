// https://arxiv.org/pdf/1804.09007

use std::time::Duration;

use log::{info, logger};
use rand::{rngs::StdRng, SeedableRng};

use super::*;

const ITER_LIMIT: usize = 4;
const TIME_LIMIT_SECS: u64 = 600;
const NODE_LIMIT: usize = 1_000_000;

fn find_nontrivial_random_extract(eg: &CHCEGraph) -> RandomExtract {
    let mut rng = StdRng::seed_from_u64(0);

    let mut candidate_ids = eg.ids();
    candidate_ids.sort_by_key(|id| {
        let has_pred = !eg.analysis_data(*id).predNames.is_empty();
        (!has_pred, *id)
    });

    for id in candidate_ids {
        let root = AppliedId::new(id, SlotMap::identity(eg.slots(id)));
        let Ok(extract) = random_extract_with_rng(&root, eg, &mut rng) else {
            continue;
        };

        if selected_eclass_count(&extract) > 1 {
            return extract;
        }
    }

    panic!("failed to find a non-trivial CHC extraction candidate");
}

// #[test]
fn mainTest() {
    // rayon::ThreadPoolBuilder::new()
    //     .num_threads(2)
    //     .build_global()
    //     .unwrap();

    initLogger();
    let mut eg = CHCEGraph::default();
    growEGraph("tests/chc/cases/leaf_drop.txt", &mut eg);
    eg.rebuild();

    let mut runner: CHCRunner = Runner::default()
        .with_egraph(eg)
        .with_node_limit(NODE_LIMIT)
        .with_time_limit(Duration::from_secs(TIME_LIMIT_SECS));

    let rewriteList = RewriteList::default();
    let rewrites = getAllRewrites(
        &rewriteList,
        RewriteOption {
            doConstraintRewrite: true,
            doFolding: true,
            doADTDefine: true,
            doPairingDefine: false,
        },
    );
    runner.prepareRun(&rewrites);
    if LOG {
        dumpCHCEGraph(&runner.egraph, "leafdrop_0.dump");
    }
    let t: _ = time(|| {
        // define
        runner.run_one(&rewrites);
        // unfold
        runner.run_one(&rewrites);
        runner.egraph.to_dot_file("leafDrop_1.dot");
        dumpCHCEGraph(&runner.egraph, "leafdrop_1.dump");
        checkCHCExists("tests/chc/cases/leaf_drop_1.txt", &runner.egraph);
        // runner.run_one(&mut getAllRewrites(
        //     &rewriteList,
        //     RewriteOption {
        //         doConstraintRewrite: true,
        //         doFolding: true,
        //         doADTDefine: true,
        //         doPairingDefine: false,
        //     },
        // ));
        // runner.run_one(&mut getAllRewrites(
        //     &rewriteList,
        //     RewriteOption {
        //         doConstraintRewrite: true,
        //         doFolding: true,
        //         doADTDefine: true,
        //         doPairingDefine: false,
        //     },
        // ))
    });

    info!("total time = {t:?}");

    info!("Egraph after");
    logCHCEGraph(&runner.egraph);

    checkCHCExists("tests/chc/cases/leaf_drop_out.txt", &runner.egraph);

    // let extract = find_nontrivial_random_extract(&runner.egraph);
    // assert_random_extract_is_closed(&extract, &runner.egraph);
}
