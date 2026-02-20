use rustsat::{
    instances::{Clause, SatInstance},
    solvers::cadical::CaDiCal,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut instance = SatInstance::new();
    let x1 = instance.new_lit(); // Variable 1
    let x2 = instance.new_lit(); // Variable 2

    // Clauses: (x1 \/ x2), (~x1 \/ x2), (x1)
    instance.add_clause(&[x1, x2]);
    instance.add_clause(&[!x1, x2]);
    instance.add_unit(x1);

    let mut solver = CaDiCal::default();
    solver.add_instance(&instance)?; // Load instance
    match solver.solve()? {
        rustsat::SolveResult::Sat => {
            println!(
                "SAT: x1={}, x2={}",
                solver.lit_val(x1)?,
                solver.lit_val(x2)?
            );
        }
        rustsat::SolveResult::Unsat => println!("UNSAT"),
        rustsat::SolveResult::Timeout => println!("Timeout"),
        _ => {}
    }
    Ok(())
}
