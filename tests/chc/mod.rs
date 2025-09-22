#![allow(unused)]
#![allow(non_snake_case)]

use crate::*;
use slotted_egraphs::*;

define_language! {
    pub enum Fgh {
        F(Slot, Slot, Slot) = "f",
        G(Slot, Slot, Slot) = "g",
        H(Vec<Slot>) = "h",
    }
}

#[test]
fn transitive_symmetry() {
    let eg: &mut EGraph<Fgh> = &mut EGraph::default();
    equate("(f $1 $2 $3)", "(g $2 $1 $3)", eg);
    equate("(g $1 $2 $3)", "(h <$1 $2 $3>)", eg);
    eg.dump();
    explain("(f $1 $2 $3)", "(h <$2 $1 $3>)", eg);
}
