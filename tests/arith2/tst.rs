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

    let a = genStr(100);
    let mut eg = EGraph::<Arith2>::default();
    id(&a, &mut eg);

    let mut runner: Runner<Arith2> = Runner::default().with_egraph(eg).with_iter_limit(60);
    let (report, t): (Report, _) = time(|| runner.run(&get_all_rewrites2()));
}
