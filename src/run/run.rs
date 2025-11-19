use crate::*;
use std::time::{Duration, Instant};

// TODO: Turn this into a nicer interface like egg's `Runner`.

pub fn run_eqsat<L: Language, N: Analysis<L>, F>(
    egraph: &mut EGraph<L, N>,
    rws: Vec<Rewrite<L, N>>,
    iter_limit: usize,
    time_limit: usize,
    mut hook: F,
) -> Report
where
    F: FnMut(&mut EGraph<L, N>) -> Result<(), String> + 'static,
{
    let start_time = Instant::now();
    let mut searchTime = Duration::new(0, 0);
    let mut applyTime = Duration::new(0, 0);
    let rebuildTime = Duration::new(0, 0);
    let mut iterations = 0;
    let stop_reason: StopReason;

    loop {
        let (did_change, search_time, apply_time) = apply_rewrites(egraph, &rws);
        searchTime += search_time;
        applyTime += apply_time;

        if egraph.total_number_of_nodes() == 0 {
            stop_reason = StopReason::Saturated;
            break;
        }

        match hook(egraph) {
            Ok(_) => (),
            Err(msg) => {
                stop_reason = StopReason::Other(msg.to_string());
                break;
            }
        }

        if !did_change {
            stop_reason = StopReason::Saturated;
            break;
        }

        if iterations >= iter_limit {
            stop_reason = StopReason::IterationLimit;
            break;
        }

        if start_time.elapsed().as_secs() >= time_limit.try_into().unwrap() {
            stop_reason = StopReason::TimeLimit;
            break;
        }

        iterations += 1;
    }

    Report {
        iterations,
        stop_reason,
        egraph_nodes: egraph.total_number_of_nodes(),
        egraph_classes: egraph.ids().len(),
        total_time: start_time.elapsed().as_secs_f64(),
        search_time: searchTime.as_secs_f64(),
        apply_time: applyTime.as_secs_f64(),
        rebuild_time: rebuildTime.as_secs_f64(),
    }
}
