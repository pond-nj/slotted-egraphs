/// Build a small e-graph and write its Graphviz DOT representation to
/// `egraph.dot`.  Compile with:
///
///   cargo run --example dump_dot
///   dot -Tpng egraph.dot -o egraph.png
use slotted_egraphs::*;

define_language! {
    pub enum SimpleLang {
        Add(AppliedId, AppliedId) = "add",
        Var(Slot) = "var",
        Num(u32),
    }
}

fn main() {
    let mut eg: EGraph<SimpleLang> = EGraph::new(());

    // Build: add(var($x), add(var($y), var($z)))
    eg.add_syn_expr(
        &RecExpr::parse("(add (var $x) (add (var $y) (var $z)))").unwrap(),
    );

    let dot = eg.to_dot();
    std::fs::write("egraph.dot", &dot).expect("Failed to write egraph.dot");
    println!("Written to egraph.dot");
    println!("Compile with:  dot -Tpng egraph.dot -o egraph.png");
    println!();
    print!("{}", dot);
}
