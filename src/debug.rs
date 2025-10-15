use crate::*;
use std::fmt::*;

use log::info;
use std::sync::Once;

impl Debug for Id {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "id{}", self.0)
    }
}

#[cfg(feature = "explanations")]
impl Debug for Equation {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{:?} = {:?}", self.l, self.r)
    }
}

impl Debug for SlotMap {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "(")?;
        let n = self.len();
        for (i, (x, y)) in self.iter().enumerate() {
            write!(f, "{x:?} -> {y:?}")?;
            if i < n - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, ")")
    }
}

impl Debug for AppliedId {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{:?}: {:?}", self.id, self.m)
    }
}

impl Display for AppliedId {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{:?}", self.id)
    }
}

impl<L: Language, N: Analysis<L>> Debug for EGraph<L, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.dump(f)
    }
}

// print:
impl<L: Language> std::fmt::Display for Pattern<L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::ENode(node, syntax_elems) => {
                let l = node.to_syntax();
                let n = l.len();

                if n != 1 {
                    write!(f, "(")?;
                }
                let mut se_idx = 0;
                for (i, r) in l.into_iter().enumerate() {
                    match r {
                        SyntaxElem::AppliedId(_) => {
                            write!(f, "{}", &syntax_elems[se_idx])?;
                            se_idx += 1;
                        }
                        SyntaxElem::Slot(slot) => {
                            write!(f, "{}", slot.to_string())?;
                        }
                        SyntaxElem::String(s) => {
                            write!(f, "{}", s)?;
                        }
                        SyntaxElem::Vec(_v) => {
                            todo!()
                        }
                        SyntaxElem::Star(_) => {
                            write!(f, "{}", &syntax_elems[se_idx])?;
                            assert!(se_idx == syntax_elems.len() - 1);
                        }
                    }
                    if i != n - 1 {
                        write!(f, " ")?;
                    }
                }
                if n != 1 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Pattern::PVar(p) => write!(f, "?{p}"),
            Pattern::Subst(b, x, t) => write!(f, "{b}[{x} := {t}]"),
            Pattern::Star(n) => write!(f, "*{}", n),
        }
    }
}

// impl<L: Language> std::fmt::Debug for Pattern<L> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(f, "{}", self)
//     }
// }

impl<L: Language> std::fmt::Display for RecExpr<L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", re_to_pattern(self))
    }
}

impl<L: Language> std::fmt::Debug for RecExpr<L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", re_to_pattern(self))
    }
}
