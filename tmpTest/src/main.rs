use z3::{Config, Context, SatResult, Solver, ast::Int};

fn main() {
    // Create configuration and context
    let mut cfg = Config::new();
    cfg.set_model_generation(true);
    let ctx = Context::new(&cfg);

    // Create a solver
    let solver = Solver::new(&ctx);

    // Declare integer variables x and y
    let x = Int::new_const(&ctx, "x");
    let y = Int::new_const(&ctx, "y");

    // x + y == 10
    let sum = Int::add(&ctx, &[&x, &y]);
    let c = &sum._eq(&Int::from_i64(&ctx, 10));
    solver.assert(c);

    // x > y
    solver.assert(&x.gt(&y));

    // Optionally constrain them to be non-negative
    solver.assert(&x.ge(&Int::from_i64(&ctx, 0)));
    solver.assert(&y.ge(&Int::from_i64(&ctx, 0)));

    // Check satisfiability
    match solver.check() {
        SatResult::Sat => {
            let model = solver.get_model().unwrap();
            let x_val = model.eval(&x, true).unwrap();
            let y_val = model.eval(&y, true).unwrap();
            println!("SAT:");
            println!("x = {}", x_val);
            println!("y = {}", y_val);
        }
        SatResult::Unsat => {
            println!("UNSAT");
        }
        SatResult::Unknown => {
            println!("UNKNOWN");
        }
    }
}
