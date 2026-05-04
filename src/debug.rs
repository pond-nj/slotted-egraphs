use crate::*;
use std::fmt::{self, *};

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
            write!(f, "{_x:?} -> {y:?}")?;
            // write!(f, "{y:?}")?;
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

// impl<L: Language, N: Analysis<L>> Debug for EClass<L, N> {
//     fn fmt(&self, f: &mut Formatter<'_>) -> Result {
//         self.dumpEClass(f)
//     }
// }

// impl<L: Language, N: Analysis<L>> Display for EClass<L, N> {
//     fn fmt(&self, f: &mut Formatter<'_>) -> Result {
//         self.dumpEClass(f)
//     }
// }

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    fn dumpEClass<T: fmt::Write>(&self, eclassId: Id, f: &mut T) -> Result {
        self.eclass(eclassId).unwrap().dumpEClass(f, self)
    }

    pub fn dumpEClassStr(&self, eclassId: Id) -> String {
        let mut s = String::new();
        self.dumpEClass(eclassId, &mut s).unwrap();
        s
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

// ── DOT / Graphviz dump ─────────────────────────────────────────────────────

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    /// Dump the e-graph as a Graphviz DOT string.
    ///
    /// Compile the result with:
    /// ```text
    /// dot -Tpng egraph.dot -o egraph.png
    /// ```
    ///
    /// The diagram mirrors `example/egraph diag.png`:
    /// * Each e-class is a dashed box whose header shows its free slots.
    /// * Each e-node inside a box is a rounded rectangle whose label shows
    ///   the operator followed by its slot / applied-id arguments.
    /// * Arrows connect e-nodes to the e-class they reference.
    pub fn to_dot(&self) -> String {
        let mut out = String::new();

        out.push_str("digraph egraph {\n");
        out.push_str("    compound=true;\n");
        out.push_str("    graph [fontname=\"Courier\", bgcolor=\"#f8f8f8\"];\n");
        out.push_str("    node  [fontname=\"Courier\", fontsize=11];\n");
        out.push_str("    edge  [fontname=\"Courier\"];\n\n");

        let mut ids = self.ids();
        ids.sort();

        // ── clusters (one per canonical e-class) ──────────────────────────
        for &id in &ids {
            let eclass = self.eclass(id).unwrap();

            let mut slot_order: Vec<Slot> = eclass.slots.iter().cloned().collect();
            slot_order.sort();
            let slot_str = slot_order
                .iter()
                .map(|s| format!("{}", s))
                .collect::<Vec<_>>()
                .join(", ");
            let header = if slot_str.is_empty() {
                format!("id{}:", id.0)
            } else {
                format!("({}):", slot_str)
            };

            out.push_str(&format!("    subgraph cluster_{} {{\n", id.0));
            out.push_str("        style=dashed;\n");
            out.push_str("        bgcolor=white;\n");
            // Bold HTML label for the eclass header
            out.push_str(&format!(
                "        label=<<B>{}</B>>;\n",
                dot_html_escape(&header)
            ));
            out.push_str("        labeljust=l;\n");

            // Invisible anchor so incoming edges can attach to the cluster
            out.push_str(&format!(
                "        anchor_{} [style=invis, shape=point, width=0, height=0];\n",
                id.0
            ));

            // One node per e-node inside the cluster
            let enodes: Vec<L> = self.enodes(id).into_iter().collect();
            for (idx, enode) in enodes.iter().enumerate() {
                let label = enode_dot_label(enode);
                out.push_str(&format!(
                    "        enode_{}_{}  [label={}, shape=record, style=rounded];\n",
                    id.0, idx, label
                ));
            }

            out.push_str("    }\n\n");
        }

        // ── edges (e-node → target e-class) ───────────────────────────────
        for &id in &ids {
            let enodes: Vec<L> = self.enodes(id).into_iter().collect();
            for (idx, enode) in enodes.iter().enumerate() {
                for (child_idx, applied_id) in enode.applied_id_occurrences().iter().enumerate() {
                    let target = self.find_id(applied_id.id);
                    out.push_str(&format!(
                        "    enode_{}_{}:child_{} -> anchor_{} [lhead=cluster_{}, minlen=2];\n",
                        id.0, idx, child_idx, target.0, target.0
                    ));
                }
            }
        }

        out.push_str("}\n");
        out
    }

    pub fn to_dot_file(&self, filename: &str) {
        let mut out = String::new();
        out.push_str(&self.to_dot());
        std::fs::write(filename, out).expect("Failed to write egraph.dot");
    }
}

/// Build a quoted DOT label for a single e-node using its syntax elements.
fn enode_dot_label<L: Language>(enode: &L) -> String {
    let mut label = String::new();
    let syntax = enode.to_syntax();
    let mut child_idx = 0;
    // label.push('{');
    for (i, elem) in syntax.iter().enumerate() {
        if i > 0 {
            label.push('|');
        }
        if matches!(elem, SyntaxElem::AppliedId(_)) {
            label.push_str(&format!("<child_{}> ", child_idx));
            child_idx += 1;
        }
        syntax_elem_to_label_str(elem, &mut label);
    }
    // label.push('}');
    // Return as a double-quoted DOT string
    format!("\"{}\"", label.replace('\\', "\\\\").replace('"', "\\\""))
}

fn syntax_elem_to_label_str(elem: &SyntaxElem, out: &mut String) {
    match elem {
        SyntaxElem::String(s) => out.push_str(s),
        SyntaxElem::Slot(s) => out.push_str(&format!("{}", s)),
        SyntaxElem::AppliedId(a) => {
            // Show the range of the slot map: the slots passed in as arguments
            let mut pairs: Vec<(Slot, Slot)> = a.m.iter().collect();
            pairs.sort_by_key(|(k, _)| *k);
            let inner = pairs
                .iter()
                .map(|(_, v)| format!("{}", v))
                .collect::<Vec<_>>()
                .join(", ");
            if inner.is_empty() {
                out.push_str("()");
            } else {
                out.push_str(&format!("({})", inner));
            }
        }
        SyntaxElem::Vec(v) => {
            out.push('<');
            for (i, elem) in v.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                syntax_elem_to_label_str(elem, out);
            }
            out.push('>');
        }
        SyntaxElem::Star(_) => out.push('*'),
    }
}

/// Escape characters that are special in a DOT HTML label (`<label=<…>>`).
fn dot_html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}
