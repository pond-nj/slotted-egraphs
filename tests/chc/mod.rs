#![allow(unused)]
#![allow(non_snake_case)]

use crate::*;
use env_logger::Builder;
use log::{debug, LevelFilter};
use slotted_egraphs::*;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;
use std::{default, io::Write};
use std::{string, vec};
use tracing_subscriber::{fmt, prelude::*};

mod rewrite;
pub use rewrite::*;

mod ematchQuery;
pub use ematchQuery::*;

mod leafDrop;
mod tst;

define_language! {
    // TODO(Pond): now children can only have max one vector
    // TODO: add dont care var?
    pub enum CHC {
        Var(Slot) = "var",
        // to specify types
        Int(Slot) = "int",
        Node(Slot) = "node",

        PredSyntax(Vec<AppliedId>) = "pred",
        New(AppliedId, AppliedId, Vec<AppliedIdOrStar>) = "new",
        Compose(Vec<AppliedIdOrStar>) = "compose",
        True() = "true",
        False() = "false",

        // node(x, l, r) has subtree l and r and element x at this node
        BiNode(AppliedId, AppliedId, AppliedId) = "binode",
        Leaf() = "leaf",

        // Boolean
        And(Vec<AppliedIdOrStar>) = "and",

        // Arithmetic
        Geq(AppliedId, AppliedId) = "geq",
        Leq(AppliedId, AppliedId) = "leq",
        Less(AppliedId, AppliedId) = "lt",
        Greater(AppliedId, AppliedId) = "gt",
        Eq(AppliedId, AppliedId) = "eq",
        Add(AppliedId, AppliedId) = "+",
        Minus(AppliedId, AppliedId) = "-",

        Number(u32),

        // (init predName syntax functional outputIdx)
        // use to create empty compose eclass for recursive definition
        Init(AppliedId, AppliedId, AppliedId, Vec<AppliedId>) = "init",
        // (interface predName syntax u32)
        // use for new predicate
        Interface(AppliedId, AppliedId, AppliedId) = "interface",
        PredName(String),
    }
}

#[derive(Default)]
pub struct CHCAnalysis;

// The implementation in "functionalTransformation" assumes that all the indices between 0 and max(outputIdx)
// if it's not the output, then it will be the input
#[derive(Default, Eq, PartialEq, Clone, Debug)]
pub struct FunctionalInfo {
    pub functional: bool,
    pub outputIdx: Vec<usize>,
}

// TODO: implement Debug to CHC clause using syn_enode
#[derive(Eq, PartialEq, Clone, Debug, Default)]
pub struct CHCData {
    predNames: HashSet<String>,
    varTypes: BTreeMap<Slot, VarType>,
    functionalInfo: FunctionalInfo,
}

// TODO: reimplement this to not access eclass many times
pub fn aggregateVarType(sh: &CHC, eg: &CHCEGraph) -> BTreeMap<Slot, VarType> {
    let sh = transformToEgraphNameSpace(sh, eg);
    let mut slots = sh.slots();
    let appIds = sh.applied_id_occurrences();
    let mut varTypes = BTreeMap::default();
    // debug!("slots: {:?}", slots);
    for s in slots {
        for app in &appIds {
            let appInverse = app.m.inverse();
            if let Some(mapToS) = appInverse.get(s) {
                let childEclassData = eg.analysis_data(app.id);
                let childSlotType = childEclassData.varTypes.get(&mapToS).unwrap();
                varTypes
                    .entry(s)
                    .and_modify(|vt: &mut VarType| assert!(vt == childSlotType))
                    .or_insert(childSlotType.clone());
            }
        }
    }

    if appIds.len() != 0 {
        assert!(varTypes.len() != 0);
    }

    varTypes
}

fn transformToEgraphNameSpace(sh: &CHC, eg: &CHCEGraph) -> CHC {
    if let Some(appId) = eg.lookup(sh) {
        return eg.getExactENodeInEGraph(sh);
    }

    sh.clone()
}

fn CHCDataForPrimitiveVar(sh: &CHC, eg: &CHCEGraph, returnType: VarType) -> CHCData {
    let sh = transformToEgraphNameSpace(sh, eg);
    let mut hm = BTreeMap::default();
    hm.insert(*sh.slots().iter().next().unwrap(), returnType);
    debug!("result {hm:?}");
    CHCData {
        predNames: HashSet::default(),
        varTypes: hm,
        functionalInfo: FunctionalInfo::default(),
    }
}

fn getBoolVal(eclassId: &Id, eg: &CHCEGraph) -> bool {
    let enodes = eg.enodes(*eclassId);
    let firstENode = enodes.iter().next().unwrap();
    match firstENode {
        CHC::True() => true,
        CHC::And(v) => {
            assert!(v.len() == 0);
            true
        }
        CHC::False() => false,
        _ => panic!(),
    }
}

fn getSingleENode(eclassId: &Id, eg: &CHCEGraph) -> CHC {
    let enodes = eg.enodes(*eclassId);
    assert!(enodes.len() == 1);
    enodes.iter().next().unwrap().clone()
}

fn mergeFunctionalInfo(x: FunctionalInfo, y: FunctionalInfo) -> FunctionalInfo {
    let mut functionalInfo = None;
    if x.functional && y.functional {
        assert!(x == y);
        functionalInfo = Some(x);
    } else if !x.functional {
        assert!(x.outputIdx.len() == 0);
        functionalInfo = Some(y);
    } else {
        assert!(y.outputIdx.len() == 0);
        functionalInfo = Some(x);
    }

    functionalInfo.unwrap()
}

fn mergePredNames(xPredNames: &HashSet<String>, yPredNames: &HashSet<String>) -> HashSet<String> {
    let mut newPredNames = HashSet::<String>::default();
    let xLen = xPredNames.len();
    let yLen = yPredNames.len();
    newPredNames.extend(yPredNames.clone());
    newPredNames.extend(xPredNames.clone());
    newPredNames
}

// TODO2: varType not propagate up
// TODO: internal var for each eclass
impl Analysis<CHC> for CHCAnalysis {
    type Data = CHCData;

    fn merge(x: CHCData, y: CHCData, i: Id, eg: &CHCEGraph) -> CHCData {
        let xClone = x.clone();
        let yClone = y.clone();
        let c = eg.eclass(i).unwrap();

        let newPredNames = mergePredNames(&x.predNames, &y.predNames);

        let mut newVarTypes = x.varTypes.clone();
        for (var, yVarType) in y.varTypes.iter() {
            if let Some(thisType) = newVarTypes.get(&var) {
                assert!(yVarType == thisType);
            } else {
                newVarTypes.insert(var.clone(), yVarType.clone());
            }
        }

        let eclassSlots = eg.allSlots(i);
        let newVarTypes: BTreeMap<Slot, VarType> = newVarTypes
            .into_iter()
            .filter(|(s, vt)| eclassSlots.contains(&s))
            .collect();

        if (x.varTypes.len() != 0 || y.varTypes.len() != 0) {
            if newVarTypes.len() == 0 {
                println!("x {xClone:#?}");
                println!("y {yClone:#?}");
                println!("c {c:#?}");
                let iApp = eg.mk_identity_applied_id(i);
                let iFind = eg.eclass(eg.find_applied_id(&iApp).id).unwrap();
                println!("cFind {iFind:#?}");

                assert!(newVarTypes.len() != 0);
            }
        }

        CHCData {
            predNames: newPredNames,
            varTypes: newVarTypes,
            functionalInfo: mergeFunctionalInfo(x.functionalInfo, y.functionalInfo),
        }
    }

    fn make(eg: &CHCEGraph, sh: &CHC) -> CHCData {
        // debug!("calling make on {:?}", sh);
        let mut chcData = match sh {
            CHC::Init(predNameId, predSyntaxId, _, _)
            | CHC::Interface(predNameId, predSyntaxId, _) => {
                let stringEnodes = eg.enodes(predNameId.id);
                assert!(stringEnodes.len() == 1);
                let stringEnode = stringEnodes.iter().next().unwrap();
                let CHC::PredName(predName) = stringEnode else {
                    panic!();
                };
                let mut predNames = HashSet::default();
                predNames.insert(predName.to_owned());

                CHCData {
                    predNames,
                    varTypes: aggregateVarType(sh, eg),
                    functionalInfo: FunctionalInfo::default(),
                }
            }
            CHC::Int(_) => CHCDataForPrimitiveVar(sh, eg, VarType::Int),
            CHC::Node(_) => CHCDataForPrimitiveVar(sh, eg, VarType::Node),
            CHC::Var(_) => CHCDataForPrimitiveVar(sh, eg, VarType::Unknown),
            _ => CHCData {
                predNames: HashSet::default(),
                varTypes: aggregateVarType(sh, eg),
                functionalInfo: FunctionalInfo::default(),
            },
        };

        let functionalInfo = match sh {
            CHC::Init(_, _, functional, outputIdxAppIds) => {
                let functional = getBoolVal(&functional.id, eg);

                let mut outputIdx: Vec<usize> = vec![];
                for appId in outputIdxAppIds {
                    let enode = getSingleENode(&appId.id, eg);
                    match enode {
                        CHC::Number(idx) => {
                            outputIdx.push(idx as usize);
                        }
                        _ => panic!(),
                    }
                }

                FunctionalInfo {
                    functional,
                    outputIdx,
                }
            }
            _ => FunctionalInfo::default(),
        };

        chcData.functionalInfo = functionalInfo;
        chcData
    }

    fn modify(eg: &mut EGraph<CHC, Self>, i: Id) {}
}

pub fn dumpCHCEClass(
    i: Id,
    map: &mut BTreeMap<AppliedId, RecExpr<CHC>>,
    eg: &CHCEGraph,
) {
    let nodes = eg.enodes(i);
    if nodes.len() == 0 {
        return;
    }

    let mut slot_order: Vec<Slot> = eg.slots(i).into();
    slot_order.sort();
    let slot_str = slot_order
        .iter()
        .map(|x| x.to_string())
        .collect::<Vec<_>>()
        .join(", ");

    let synExpr = eg.getSynExpr(&i, map);
    print!("\n{}", synExpr);
    print!("\n{:?}", eg.analysis_data(i));
    print!("\n{:?}({}):", i, &slot_str);
    print!(">> {:?}\n", eg.getSynNodeNoSubst(&i));

    for node in eg.enodes(i) {
        print!(" - {node:?}\n");
        let (sh, m) = node.weak_shape();
        print!(" -   {sh:?}\n");
    }
    let permute = eg.getSlotPermutation(&i);
    for p in permute {
        print!(" -- {:?}\n", p);
    }
}

pub fn dumpCHCEGraph(eg: &CHCEGraph) {
    print!("\n == Egraph ==");
    let mut eclasses = eg.ids();
    eclasses.sort();

    let mut map = BTreeMap::<AppliedId, RecExpr<CHC>>::default();
    for i in eclasses {
        dumpCHCEClass(i, &mut map, eg);
    }
    print!("");
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
