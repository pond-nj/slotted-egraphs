use std::time::Duration;

use crate::*;
use log::debug;
use serial_test::serial;

/// Test with many permutations of commutative operations
/// sortENodesByNT should help by grouping canonical forms of equivalent expressions
/// This creates E-nodes that benefit from being in canonical form during rewriting
#[test]
#[serial]
fn t_canonical_commutativity() {
    initLogger();

    let mut eg = EGraph::<Arith2>::default();

    // Create multiple equivalent expressions written in different orders
    // All of these are semantically equivalent but syntactically different
    // sortENodesByNT should group them canonically for efficient rewriting

    let exprs = vec![
        // Different permutations of: (a + b) + (c + d)
        "(add (add (var $0) (var $1)) (add (var $2) (var $3)))",
        "(add (add (var $1) (var $0)) (add (var $3) (var $2)))",
        "(add (add (var $2) (var $3)) (add (var $0) (var $1)))",
        "(add (add (var $3) (var $2)) (add (var $1) (var $0)))",
        // Different permutations of: (a + c) + (b + d)
        "(add (add (var $0) (var $2)) (add (var $1) (var $3)))",
        "(add (add (var $2) (var $0)) (add (var $3) (var $1)))",
        "(add (add (var $1) (var $3)) (add (var $0) (var $2)))",
        "(add (add (var $3) (var $1)) (add (var $2) (var $0)))",
        // Different permutations of: (a + d) + (b + c)
        "(add (add (var $0) (var $3)) (add (var $1) (var $2)))",
        "(add (add (var $3) (var $0)) (add (var $2) (var $1)))",
        "(add (add (var $1) (var $2)) (add (var $0) (var $3)))",
        "(add (add (var $2) (var $1)) (add (var $3) (var $0)))",
        // Repeat the patterns multiple times to stress-test the canonical ordering
        "(add (add (var $0) (var $1)) (add (var $2) (var $3)))",
        "(add (add (var $1) (var $0)) (add (var $3) (var $2)))",
        "(add (add (var $2) (var $3)) (add (var $0) (var $1)))",
        "(add (add (var $3) (var $2)) (add (var $1) (var $0)))",
        // Triple-nested permutations
        "(add (add (add (var $0) (var $1)) (var $2)) (var $3))",
        "(add (add (add (var $1) (var $0)) (var $3)) (var $2))",
        "(add (add (add (var $2) (var $3)) (var $0)) (var $1))",
        "(add (add (add (var $3) (var $2)) (var $1)) (var $0))",
    ];

    // Add all expressions to the e-graph
    for expr in &exprs {
        let _ = id(expr, &mut eg);
    }

    println!("Initial egraph nodes: {}", eg.total_number_of_nodes());
    println!("Initial egraph classes: {}", eg.totalNumberOfEclass());

    // Run saturation with commutative rewrites
    // sortENodesByNT should help the rewrite engine find and combine equivalent terms
    let mut runner: Runner<Arith2> = Runner::default()
        .with_egraph(eg)
        .with_iter_limit(10)
        .with_node_limit(100_000)
        .with_time_limit(Duration::from_secs(300));

    let (report, t): (Report, _) = time(|| runner.run(&get_all_rewrites2()));

    println!("report {report:?}");
    println!(
        "final egraph size {}",
        runner.egraph.total_number_of_nodes()
    );
    println!(
        "final egraph classes {}",
        runner.egraph.totalNumberOfEclass()
    );

    // Count specific node types
    let mut count_add = 0;
    let mut count_add_long = 0;
    for id in runner.egraph.ids() {
        let enodes = runner.egraph.enodes(id);
        for enode in enodes {
            match enode {
                Arith2::Add(..) => count_add += 1,
                Arith2::AddLong(_) => count_add_long += 1,
                _ => {}
            }
        }
    }
    println!("count add nodes {}", count_add);
    println!("count addLong nodes {}", count_add_long);
    println!("total time = {t:?}");
}

/// Test with deeply nested commutative operations
/// This creates a larger search space where canonical ordering helps prune equivalent branches
#[test]
#[serial]
fn t_canonical_deep_nesting() {
    initLogger();

    let mut eg = EGraph::<Arith2>::default();

    // Generate expressions with different nesting orders, all equivalent
    // Example: (((a + b) + c) + d) vs ((a + (b + c)) + d) vs (a + ((b + c) + d)) etc.

    fn gen_nested_expr(vars: Vec<usize>, order: &[usize]) -> String {
        if order.len() == 1 {
            format!("(var ${})", vars[order[0]])
        } else if order.len() == 2 {
            format!("(add (var ${}) (var ${}))", vars[order[0]], vars[order[1]])
        } else {
            let mid = order.len() / 2;
            format!(
                "(add {} {})",
                gen_nested_expr(vars.clone(), &order[..mid]),
                gen_nested_expr(vars.clone(), &order[mid..])
            )
        }
    }

    let vars = vec![0, 1, 2, 3, 4];

    // Generate different orderings of the same variables
    let orderings = vec![
        vec![0, 1, 2, 3, 4],
        vec![1, 0, 3, 2, 4],
        vec![2, 3, 0, 1, 4],
        vec![4, 3, 2, 1, 0],
        vec![0, 2, 1, 4, 3],
        vec![3, 1, 4, 0, 2],
    ];

    for ordering in orderings {
        let expr = gen_nested_expr(vars.clone(), &ordering);
        let _ = id(&expr, &mut eg);
    }

    println!("Initial egraph nodes: {}", eg.total_number_of_nodes());

    let mut runner: Runner<Arith2> = Runner::default()
        .with_egraph(eg)
        .with_iter_limit(5)
        .with_node_limit(50_000)
        .with_time_limit(Duration::from_secs(300));

    let (report, t): (Report, _) = time(|| runner.run(&get_all_rewrites2()));

    println!("report {report:?}");
    println!(
        "final egraph size {}",
        runner.egraph.total_number_of_nodes()
    );
    println!("total time = {t:?}");
}
