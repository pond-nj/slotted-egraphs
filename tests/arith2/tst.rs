use std::time::Duration;

use crate::*;
use log::debug;
use serial_test::serial;

fn genStr(n: usize) -> String {
    if n == 0 {
        return "(var $0)".to_string();
    }
    format!("(add (var ${}) {})", n - 1, genStr(n - 1))
}

#[test]
#[serial]
fn t7() {
    initLogger();

    let a = genStr(10);
    println!("a {}", a);
    let mut eg = EGraph::<Arith2>::default();
    id(&a, &mut eg);

    let mut runner: Runner<Arith2> = Runner::default()
        .with_egraph(eg)
        .with_iter_limit(4)
        .with_node_limit(1_000_000)
        .with_time_limit(Duration::from_secs(600));
    let (report, t): (Report, _) = time(|| runner.run(&get_all_rewrites2()));
    println!("report {report:?}");
    println!("egraph size {}", runner.egraph.total_number_of_nodes());
    let mut count = 0;
    for id in runner.egraph.ids() {
        let enodes = runner.egraph.enodes(id);
        for enode in enodes {
            if let Arith2::AddLong(_) = enode {
                count += 1;
            }
        }
    }
    println!("count addLong {}", count);
    println!("total time = {t:?}");
}
