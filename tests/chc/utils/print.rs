use super::*;

use std::fs::File;
use std::io::{self, BufWriter, Write};

// ── RecExpr<CHC> → CHC AST pretty-printer ────────────────────────────────────
//
// Converts the S-expression syn-expr back into Prolog-style text by
// constructing the same CHC AST types (Term, Constr, PredApp, CHCRule) that
// are used in chcAST.rs and delegating formatting to their Display impls.
// This means display logic only needs to be maintained in one place.

fn slot_to_chcvar(slot: &Slot) -> CHCVar {
    // Slot displays as "$name"; strip the leading '$' to recover the var name.
    let s = format!("{}", slot);
    CHCVar::Str(s.trim_start_matches('$').to_string())
}

/// Convert a RecExpr node that acts as a *term* (variable, number, or
/// arithmetic/data constructor) into the CHC AST Term type.
fn recexpr_to_term(expr: &RecExpr<CHC>) -> Term {
    match &expr.node {
        CHC::IntType(s) | CHC::NodeType(s) | CHC::ListType(s) => Term::Var(slot_to_chcvar(s)),
        CHC::Number(n) => Term::Var(CHCVar::Int(*n as i32)),
        CHC::Leaf() => Term::Constr(Constr {
            op: ConstrOP::Leaf,
            args: vec![],
        }),
        CHC::EmptyList() => Term::Constr(Constr {
            op: ConstrOP::EmptyList,
            args: vec![],
        }),
        CHC::BiNode(_, _, _) => Term::Constr(Constr {
            op: ConstrOP::Binode,
            args: expr.children.iter().map(recexpr_to_term).collect(),
        }),
        CHC::List(_, _) => Term::Constr(Constr {
            op: ConstrOP::List,
            args: expr.children.iter().map(recexpr_to_term).collect(),
        }),
        CHC::Add(_, _) => Term::Constr(Constr {
            op: ConstrOP::Add,
            args: expr.children.iter().map(recexpr_to_term).collect(),
        }),
        CHC::Minus(_, _) => Term::Constr(Constr {
            op: ConstrOP::Minus,
            args: expr.children.iter().map(recexpr_to_term).collect(),
        }),
        _ => panic!(),
    }
}

/// Convert a RecExpr node that acts as a *constraint* (comparison or
/// arithmetic) into the CHC AST Constr type.
fn recexpr_to_constr(expr: &RecExpr<CHC>) -> Constr {
    let op = match &expr.node {
        CHC::Eq(_, _) => ConstrOP::Eq,
        CHC::Neq(_, _) => ConstrOP::Neq,
        CHC::Geq(_, _) => ConstrOP::Geq,
        CHC::Leq(_, _) => ConstrOP::Leq,
        CHC::Less(_, _) => ConstrOP::Lt,
        CHC::Greater(_, _) => ConstrOP::Gt,
        CHC::Add(_, _) => ConstrOP::Add,
        CHC::Minus(_, _) => ConstrOP::Minus,
        _ => panic!(),
    };
    Constr {
        op,
        args: expr.children.iter().map(recexpr_to_term).collect(),
    }
}

// TOrev
/// Convert a ComposeInit RecExpr (a body predicate reference) to PredApp.
fn recexpr_to_predapp(expr: &RecExpr<CHC>) -> Option<PredApp> {
    let CHC::ComposeInit(_, _, _, _) = &expr.node else {
        return None;
    };
    let pred_name = match &expr.children.first()?.node {
        CHC::PredName(s) => s.clone(),
        _ => return None,
    };
    // children[1] is the Head([typed_slot, ...]) node
    let args: Vec<Term> = expr
        .children
        .get(1)?
        .children
        .iter()
        .map(recexpr_to_term)
        .collect();
    Some(PredApp {
        pred_name,
        args: Args::new(args),
    })
}

/// Convert a Clause RecExpr into a CHCRule.  The head predicate name is
/// unknown at this level, so callers pass a placeholder (e.g. `"?"`).
fn recexpr_clause_to_str(expr: &RecExpr<CHC>, head_pred: &str) -> String {
    let CHC::Clause(_, _, _) = &expr.node else {
        panic!();
    };
    // children[0] = Head([typed_slots])
    // children[1] = And([constraint_exprs])
    // children[2..] = body ComposeInit exprs
    let head_args: Vec<Term> = expr
        .children
        .first()
        .unwrap()
        .children
        .iter()
        .map(recexpr_to_term)
        .collect();
    let constrs: Vec<String> = expr
        .children
        .get(1)
        .unwrap()
        .children
        .iter()
        .map(|c| format!("{}", recexpr_to_constr(c)))
        .collect();
    let body_def: Vec<String> = expr.children[2..].iter().map(synExprToProlog).collect();
    let head = PredApp {
        pred_name: head_pred.to_string(),
        args: Args::new(head_args),
    };

    format!("{head} [{}] [{}]", constrs.join(", "), body_def.join(", "))
}

/// Pretty-print a syn-expr in Prolog/CHC notation, delegating the actual
/// formatting to the existing Display impls in chcAST.rs.
pub fn synExprToProlog(expr: &RecExpr<CHC>) -> String {
    match &expr.node {
        // A predicate reference: show as "predName(arg1, arg2, ...)"
        CHC::ComposeInit(_, _, _, _) => {
            let pred_name = match &expr.children.first().unwrap().node {
                CHC::PredName(s) => s.as_str(),
                _ => panic!(),
            };
            let args: Vec<String> = expr
                .children
                .get(1)
                .unwrap()
                .children
                .iter()
                .map(|c| format!("{}", recexpr_to_term(c)))
                .collect();
            format!("{}({})", pred_name, args.join(", "))
        }
        // A collection of clauses: show each clause on its own line
        CHC::Compose(_) => {
            let lines: Vec<String> = expr
                .children
                .iter()
                .map(|c| format!("{}", recexpr_clause_to_str(c, "?")))
                .collect();
            if lines.is_empty() {
                "(empty compose)".to_string()
            } else {
                lines.join("\n")
            }
        }
        // A single clause: head predicate name is unknown, use "?"
        CHC::Clause(_, _, _) => format!("{}", recexpr_clause_to_str(expr, "?")),
        // Anything else: fall back to the existing S-expression display
        CHC::And(_) => {
            let constrs: Vec<String> = expr
                .children
                .iter()
                .map(|c| format!("{}", recexpr_to_constr(c)))
                .collect();
            format!("[{}]", constrs.join(", "))
        }
        _ => format!("{}", expr),
    }
}

fn writeCHCEClass(
    i: Id,
    map: &mut BTreeMap<AppliedId, RecExpr<CHC>>,
    eqvIds: &BTreeMap<Id, Vec<Id>>,
    eg: &CHCEGraph,
    writer: &mut impl Write,
) -> io::Result<()> {
    let nodes = eg.enodes(i);
    if nodes.len() == 0 {
        return Ok(());
    }

    let mut slot_order: Vec<Slot> = eg.slots(i).clone().into();
    let mut slot_sorted = slot_order.clone();
    slot_sorted.sort();
    assert!(slot_order == slot_sorted);
    let slot_str = slot_order
        .iter()
        .map(|x| x.to_string())
        .collect::<Vec<_>>()
        .join(", ");

    // TODO: this function uses too much memory
    let calls = &mut BTreeMap::new();
    let syn_str = match eg.getSynExpr(&i, map, calls) {
        Ok(expr) => synExprToProlog(expr),
        Err(e) => e,
    };
    write!(writer, "\n{}", syn_str)?;
    write!(writer, "\n{:?}", eg.analysis_data(i))?;
    write!(writer, "\n{:?}({:?})({}):", i, eqvIds[&i], &slot_str)?;
    write!(writer, ">> {:?}\n", eg.getSynNodeNoSubst(&i))?;

    let mut eclassNodes: Vec<_> = eg.enodes(i).into_iter().collect();
    eclassNodes.sort();

    for node in eclassNodes {
        writeln!(writer, " - {node:?}")?;
        // let (sh, m) = node.weak_shape();
        // print!(" >-  {sh:?}\n");
        // let (sh, m) = weakShapeCHC(&node);
        // print!(" - or  {sh:?}\n");
    }
    let permute = eg.getSlotPermutation(&i);
    for p in permute {
        writeln!(writer, " -- {:?}", p)?;
    }

    Ok(())
}

fn writeCHCEGraph(eg: &CHCEGraph, writer: &mut impl Write) -> io::Result<()> {
    write!(writer, "\n == Egraph ==")?;
    write!(writer, "\n size of egraph: {}", eg.total_number_of_nodes())?;
    let mut eclasses = eg.ids();
    write!(writer, "\n number of eclasses: {}", eclasses.len())?;
    eclasses.sort();

    // TODO: it's possible that map is using too much memory
    let mut map = BTreeMap::<AppliedId, RecExpr<CHC>>::default();
    let eqvIds = eg.buildEqvIds();
    for i in eclasses {
        writeCHCEClass(i, &mut map, &eqvIds, eg, writer)?;
    }

    writer.flush()
}

// pub fn dumpCHCEClass(
//     i: Id,
//     map: &mut BTreeMap<AppliedId, RecExpr<CHC>>,
//     eqvIds: &BTreeMap<Id, Vec<Id>>,
//     eg: &CHCEGraph,
// ) {
//     let stdout = io::stdout();
//     let mut writer = stdout.lock();
//     writeCHCEClass(i, map, eqvIds, eg, &mut writer).expect("failed to write CHC eclass dump");
// }

pub fn printCHCEGraph(eg: &CHCEGraph) {
    let stdout = io::stdout();
    let mut writer = stdout.lock();
    writeCHCEGraph(eg, &mut writer).expect("failed to print CHC egraph");
}

pub fn dumpCHCEGraph(eg: &CHCEGraph, path: impl AsRef<std::path::Path>) -> io::Result<()> {
    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);
    writeCHCEGraph(eg, &mut writer)
}

// pub fn printENode(enode: &CHC, eg: &CHCEGraph) {
//     let stdout = io::stdout();
//     let mut writer = stdout.lock();

//     // enode can be a newly defined one, it might not exist in the egraph
//     let eclassId = eg.lookup(&enode);

//     writeln!(writer, "Enode {enode:?}").expect("failed to print enode");

//     let map = &mut BTreeMap::<AppliedId, RecExpr<CHC>>::default();
//     if eclassId.is_some() {
//         let eclassId = eclassId.unwrap();
//         let calls = &mut BTreeMap::new();
//         let synExpr = eg.getSynExpr(&eclassId.id, map, calls).unwrap();
//         writeln!(writer, "Inside eclass {eclassId:?}: ").expect("failed to print eclass header");
//         writeln!(writer, "{}", synExprToProlog(synExpr)).expect("failed to print syn expr");
//     }

//     let eqvIds = eg.buildEqvIds();
//     writeln!(writer, "child eclass: ").expect("failed to print child header");
//     for child in enode.applied_id_occurrences() {
//         writeCHCEClass(child.id, map, &eqvIds, eg, &mut writer)
//             .expect("failed to print child eclass");
//         writeln!(writer).expect("failed to print line break");
//     }
// }
