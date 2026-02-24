use crate::*;
use std::fmt::*;

use log::info;
use std::sync::Once;

impl Debug for Id {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "id{}", self.0)
    }
}

impl Display for Id {
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

impl Display for SlotMap {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "(")?;
        let n = self.len();
        for (i, (_x, y)) in self.iter().enumerate() {
            // write!(f, "{x:?} -> {y:?}")?;
            write!(f, "{y:?}")?;
            if i < n - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, ")")
    }
}

#[cfg(not(feature = "originalPrint"))]
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

#[cfg(feature = "originalPrint")]
impl Debug for SlotMap {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "[")?;
        let n = self.len();
        for (i, (x, y)) in self.iter().enumerate() {
            write!(f, "{x:?} -> {y:?}")?;
            if i < n - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, "]")
    }
}

#[cfg(not(feature = "originalPrint"))]
impl Debug for AppliedId {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{:?}: {}", self.id, self.m)
    }
}

#[cfg(feature = "originalPrint")]
impl Debug for AppliedId {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{:?}{:?}", self.id, self.m)
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

impl<L: Language, N: Analysis<L>> Display for EGraph<L, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.dump(f)
    }
}

impl<L: Language, N: Analysis<L>> Debug for EClass<L, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.dumpEClass(f)
    }
}

impl<L: Language, N: Analysis<L>> Display for EClass<L, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.dumpEClass(f)
    }
}

fn writeSyntaxElem<L: Language>(
    r: SyntaxElem,
    children: &Vec<Pattern<L>>,
    se_idx: &mut usize,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    match r {
        SyntaxElem::AppliedId(_) => {
            write!(f, "{}", &children[*se_idx])?;
            *se_idx += 1;
        }
        SyntaxElem::Slot(slot) => {
            write!(f, "{}", slot.to_string())?;
        }
        SyntaxElem::String(s) => {
            write!(f, "{}", s)?;
        }
        SyntaxElem::Vec(v) => {
            write!(f, "<")?;
            let n = v.len();
            for (i, s) in v.into_iter().enumerate() {
                writeSyntaxElem(s, children, se_idx, f)?;
                if i != n - 1 {
                    write!(f, " ")?;
                }
            }
            write!(f, ">")?;
        }
        SyntaxElem::Star(_) => {
            write!(f, "{}", &children[*se_idx])?;
            assert!(*se_idx == children.len() - 1);
        }
    }

    Ok(())
}

// print:
impl<L: Language> std::fmt::Display for Pattern<L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::ENode(node, children) => {
                let l = node.to_syntax();
                let n = l.len();

                if n != 1 || matches!(l[0], SyntaxElem::String(_)) {
                    write!(f, "(")?;
                }
                let mut se_idx = 0;
                for (i, r) in l.clone().into_iter().enumerate() {
                    writeSyntaxElem(r, children, &mut se_idx, f)?;
                    if i != n - 1 {
                        write!(f, " ")?;
                    }
                }
                if n != 1 || matches!(l[0], SyntaxElem::String(_)) {
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
