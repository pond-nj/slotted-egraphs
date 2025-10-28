use crate::*;
use log::debug;
use serial_test::serial;

#[test]
#[serial]
fn t1() {
    initLogger();
    // x+y = y+x
    let x = "$0";
    let y = "$1";

    let a = &format!("(add (var {x}) (var {y}))");
    let b = &format!("(add (var {y}) (var {x}))");

    assert_reaches(a, b, &get_all_rewrites()[..], 3);
}

#[test]
#[serial]
fn t2() {
    initLogger();
    // (x+y) * (x+y) = (x+y) * (y+x)
    let x = "$0";
    let y = "$1";
    let z = "$2";

    let a = &format!("(mul (add (var {x}) (var {y})) (add (var {x}) (var {y})))");
    let b = &format!("(mul (add (var {x}) (var {y})) (add (var {y}) (var {x})))");

    assert_reaches(a, b, &get_all_rewrites()[..], 2);
}

#[test]
#[serial]
fn t3() {
    initLogger();
    // (x+y) * (y+z) = (z+y) * (y+x)
    let x = "$0";
    let y = "$1";
    let z = "$2";

    let a = &format!("(mul (add (var {x}) (var {y})) (add (var {y}) (var {z})))");
    let b = &format!("(mul (add (var {z}) (var {y})) (add (var {y}) (var {x})))");

    assert_reaches(a, b, &get_all_rewrites()[..], 3);
}

#[test]
#[serial]
fn t4() {
    initLogger();
    // (x+y)**2 = x**2 + x*y + x*y + y**2
    // let a = "(mul (add (var $x) (var $y)) (add (var $x) (var $y)))";
    // let b = "(add (mul (var $x) (var $x))
    //          (add (mul (var $x) (var $y))
    //          (add (mul (var $x) (var $y))
    //               (mul (var $y) (var $y))
    //          )))";
    // assert_reaches(a, b, &get_all_rewrites()[..], 10);

    let a = "(mul (add (var $x) (var $y)) (add (var $x) (var $y)))";
    let mut eg = EGraph::<Arith>::default();
    id(&a, &mut eg);

    let mut runner: Runner<Arith> = Runner::default().with_egraph(eg).with_iter_limit(60);
    debug!("eg after {:?}", runner.egraph);

    let aAbstract = "(mul (add ?a ?b) (add ?a ?b))";
    let result = ematch_all(&runner.egraph, &Pattern::parse(&aAbstract).unwrap());
    debug!("match result1 = {result:?}");
}

fn add_chain(it: impl Iterator<Item = usize>) -> String {
    let mut it = it.map(|u| format!("(var ${u})"));
    let mut x = format!("{}", it.next().unwrap());
    for y in it {
        x = format!("(add {x} {y})");
    }
    x
}

#[test]
#[serial]
#[cfg_attr(feature = "explanations", ignore = "TODO: fails")]
fn t5() {
    initLogger();
    // x0+...+xN = xN+...+x0
    // This times out for larger N!
    // TODO reset N to 7.
    const N: usize = 4;

    let a = &add_chain(0..=N);
    let b = &add_chain((0..=N).rev());

    assert_reaches(a, b, &get_all_rewrites()[..], 10);
}

#[test]
#[serial]
fn t6() {
    initLogger();
    // z*(x+y) = z*(y+x)
    let x = "$0";
    let y = "$1";
    let z = "$2";

    let a = &format!("(mul (var {z}) (add (var {x}) (var {y})))");
    let b = &format!("(mul (var {z}) (add (var {y}) (var {x})))");
    assert_reaches(a, b, &[add_comm()], 10);
}

#[test]
#[serial]
fn t7() {
    initLogger();

    let a = "(add 2 (var $0))";
    let mut eg = EGraph::<Arith>::default();
    id(&a, &mut eg);

    let mut runner: Runner<Arith> = Runner::default().with_egraph(eg).with_iter_limit(60);
    debug!("eg after {:?}", runner.egraph);

    let aAbstract = "(add 3 ?a)";
    let result = ematch_all(&runner.egraph, &Pattern::parse(&aAbstract).unwrap());
    debug!("match result1 = {result:?}");
}
