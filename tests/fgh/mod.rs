#![allow(unused)]
#![allow(non_snake_case)]

use crate::*;
use log::debug;
use slotted_egraphs::*;

define_language! {
    pub enum Fgh {
        F(Slot, Slot) = "f",
        G(Slot, Slot) = "g",
        H(Slot, Slot) = "h",
    }
}

#[test]
fn transitive_symmetry() {
    let eg: &mut EGraph<Fgh> = &mut EGraph::default();
    equate("(f $1 $2)", "(g $2 $1)", eg);
    equate("(g $1 $2)", "(h $1 $2)", eg);
    println!("eg = {eg:?}");
    explain("(f $1 $2)", "(h $2 $1)", eg);
}
