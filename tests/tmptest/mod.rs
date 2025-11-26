use crate::*;

define_language! {
    pub enum Tmp {
        Var(Slot) = "var",

        Add(AppliedId, AppliedId) = "add",

        // rest:
        Number(u32),
        Symbol(Symbol),
    }
}

#[test]
fn test() {
    let mut eg = EGraph::<Tmp>::default();
    let a = eg.add_expr(RecExpr::parse("(add (var $0) (var $1))").unwrap());
    let b = eg.add_expr(RecExpr::parse("(add (var $1) (var $1))").unwrap());
    println!("egraph = {:?}", eg);
}
