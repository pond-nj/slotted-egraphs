#![allow(unused)]
#![allow(non_snake_case)]

use crate::*;
use log::{debug, LevelFilter};
use slotted_egraphs::*;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;
use std::thread;
use std::{default, io::Write};
use std::{string, vec};

mod rewrite;
pub use rewrite::*;

mod utils;
pub use utils::*;

mod ast;
pub use ast::*;

mod analysis;
pub use analysis::*;

// test
mod leafDrop;
pub use leafDrop::*;

mod pairingPaperArray;
mod synchronizedCHC;
mod unitTest;

define_language! {
    // TODO(Pond): now children can only have max one vector
    pub enum CHC {
        // to specify types
        // TODO: this doesn't allow dynamic type, e.g. if we want list of type T
        IntType(Slot) = "intType",
        NodeType(Slot) = "nodeType",
        ListType(Slot) = "listType",
        // TODO: if add new ADT type, must also change some function in rewrite phase - definition

        // wouldn't sort this
        PredSyntax(Vec<AppliedId>) = "pred",
        // TODO: if we change new enode predicate body, would it be better for sorting?
        New(AppliedId, AppliedId, OrderVec<AppliedIdOrStar>) = "new",
        Compose(OrderVec<AppliedIdOrStar>) = "compose",
        True() = "true",
        False() = "false",

        // node(x, l, r) has subtree l and r and element x at this node
        BiNode(AppliedId, AppliedId, AppliedId) = "binode",
        Leaf() = "leaf",
        List(AppliedId, AppliedId) = "list",
        EmptyList() = "emptyList",

        // Boolean
        And(OrderVec<AppliedIdOrStar>) = "and",

        // Arithmetic
        Geq(AppliedId, AppliedId) = "geq",
        Leq(AppliedId, AppliedId) = "leq",
        Less(AppliedId, AppliedId) = "lt",
        Greater(AppliedId, AppliedId) = "gt",
        Eq(AppliedId, AppliedId) = "eq",
        Neq(AppliedId, AppliedId) = "neq",
        Add(AppliedId, AppliedId) = "add",
        Minus(AppliedId, AppliedId) = "minus",

        Number(u32),

        // (composeInit predName syntax functional outputIdx)
        // use to create empty compose eclass for recursive definition
        ComposeInit(AppliedId, AppliedId, AppliedId, OrderVec<AppliedId>) = "composeInit",
        PredName(String),
    }
}

fn enodeToSMTOp(enode: &CHC) -> &'static str {
    match enode {
        CHC::Add(..) => "+",
        CHC::And(..) => "and",
        CHC::Eq(..) => "=",
        CHC::Greater(..) => ">",
        CHC::Geq(..) => ">=",
        CHC::Less(..) => "<",
        CHC::Leq(..) => "<=",
        CHC::BiNode(..) => "binode",

        _ => todo!(),
    }
}

fn aggregateType(pattern: &Pattern<CHC>, types: &mut BTreeMap<Slot, VarType>) {
    let Pattern::ENode(node, children) = pattern else {
        panic!()
    };

    match node {
        CHC::IntType(s) => {
            types.insert(s.clone(), VarType::Int);
        }
        CHC::NodeType(s) => {
            types.insert(s.clone(), VarType::Node);
        }
        CHC::ListType(s) => {
            types.insert(s.clone(), VarType::List);
        }
        _ => {}
    }

    for child in children {
        aggregateType(child, types);
    }
}

fn patternToSMTLib(pattern: &Pattern<CHC>) -> String {
    let mut out = String::new();
    let Pattern::ENode(node, children) = pattern else {
        panic!()
    };

    let ret = match node {
        CHC::IntType(s) => Some(s.to_string()),
        CHC::NodeType(s) => Some(s.to_string()),
        CHC::ListType(s) => Some(s.to_string()),
        CHC::Leaf() => Some("leaf".to_string()),
        CHC::Number(n) => Some(format!("{}", n)),
        _ => None,
    };

    if ret.is_some() {
        return ret.unwrap();
    }

    let op = enodeToSMTOp(node);
    let childrenExpr = children
        .iter()
        .map(|child| patternToSMTLib(child))
        .collect::<Vec<_>>()
        .join(" ");

    "(".to_string() + &op + " " + &childrenExpr + ")"
}

pub fn synSMTLibExpr(eclassId: Id, eg: &CHCEGraph) -> String {
    // TODO: get type info first
    let mut map = BTreeMap::default();
    let mut calls = BTreeMap::default();
    let expr = eg.getSynExpr(&eclassId, &mut map, &mut calls);
    if expr.is_err() {
        return expr.unwrap_err();
    }
    let pattern = re_to_pattern(expr.unwrap());

    let mut types = BTreeMap::default();
    aggregateType(&pattern, &mut types);

    let mut out = String::new();
    for (s, vt) in types {
        out += &format!("(declare-const {s} {})\n", vt.toSMT());
    }
    out += "(declare-datatypes ((tree 0)) (((binode int tree tree) (leaf))))\n";
    out += "\n\n";
    out += &patternToSMTLib(&pattern);
    out
}

pub fn getSingleENode(eclassId: &Id, eg: &CHCEGraph) -> CHC {
    let enodes = eg.enodes(*eclassId);
    assert!(enodes.len() == 1);
    enodes.iter().next().unwrap().clone()
}

fn weakShapeCHC(enode: &CHC) -> (CHC, SlotMap) {
    match enode {
        CHC::New(syntax, cond, children) => {
            let m = &mut (slotted_egraphs::SlotMap::new(), 0);

            // syntax first
            let mut updatedSyntax = syntax.clone();
            updatedSyntax.weak_shape_impl(m);

            // children next
            let mut updatedChildren = children.clone();
            updatedChildren.weak_shape_impl(m);

            // and then condition last
            let mut updatedCond = cond.clone();
            updatedCond.weak_shape_impl(m);

            (
                CHC::New(updatedSyntax, updatedCond, updatedChildren),
                m.0.inverse(),
            )
        }
        _ => enode.weak_shape(),
    }
}

pub fn merge(s1: &str, s2: &str, eg: &mut CHCEGraph) -> Id {
    let id1 = &id(&s1, eg);
    let id2 = &id(&s2, eg);
    eg.union(id1, id2);
    eg.find_applied_id(id1).id
}

pub fn starPVar(starIndex: u32, starCount: u32) -> String {
    format!("star_{}_{}", starIndex, starCount)
}

// get a string of star_i_j from the subst
pub fn starPStr(starIndex: u32, subst: &Subst) -> String {
    let mut res: Vec<String> = starPVecStr(starIndex, subst);
    for s in &mut res {
        s.insert_str(0, "?");
    }
    res.join(" ")
}

// get a vector of string of star_i_j from the subst
fn starPVecStr(starIndex: u32, subst: &Subst) -> Vec<String> {
    let mut countStar = 0;
    let mut allStarStr: Vec<String> = vec![];
    while subst.contains_key(&starPVar(starIndex, countStar)) {
        allStarStr.push((format!("{}", starPVar(starIndex, countStar))));
        countStar += 1;
    }
    allStarStr
}

// get all appliedId that is
pub fn starIds(starIndex: u32, subst: &Subst) -> Vec<AppliedId> {
    let mut allIds = vec![];
    let mut starCount = 0;
    // cannot merge this into one call because starCount gets updated
    while subst.contains_key(&starPVar(starIndex, starCount)) {
        allIds.push(subst[&starPVar(starIndex, starCount)].clone());
        starCount += 1;
    }

    allIds
}

pub fn starStrSortedByAppIds(starIndices: &[u32], subst: &Subst) -> String {
    let mut starStrs = vec![];
    for i in starIndices {
        starStrs.extend(starPVecStr(*i, subst));
    }
    starStrs.sort_by(|si, sj| subst[si].cmp(&subst[sj]));
    starStrs.iter_mut().for_each(|s| s.insert_str(0, "?"));
    starStrs.join(" ")
}

pub fn getMaxStarCount(starIndex: u32, subst: &Subst) -> u32 {
    let mut starMax = 0;
    while subst.contains_key(&starPVar(starIndex, starMax)) {
        starMax += 1;
    }

    starMax
}

type CHCEGraph = EGraph<CHC, CHCAnalysis>;
type CHCRewrite = Rewrite<CHC, CHCAnalysis>;
type CHCRunner = Runner<CHC, CHCAnalysis>;
