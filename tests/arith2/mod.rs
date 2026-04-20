#![allow(unused)]
#![allow(non_snake_case)]

use crate::*;
use log::debug;

mod tst;
pub use tst::*;

mod tst_canonical;
pub use tst_canonical::*;

mod rewrite;
pub use rewrite::*;

define_language! {
    pub enum Arith2 {
        Add(AppliedId, AppliedId) = "add",
        AddLong(OrderVec<AppliedIdOrStar>) = "addLong",
        Var(Slot) = "var",
    }
}
