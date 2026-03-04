use super::*;
use crate::*;
use derive_more::derive;
use log::{debug, error, info, trace, warn};
use std::cell::{Ref, RefCell};

use std::f32::consts::E;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};
use union_find::{QuickUnionUf, UnionBySize, UnionFind};
use vec_collections::VecSet;

static G_COUNTER: AtomicUsize = AtomicUsize::new(0);

use std::collections::HashSet;

mod unfold;
pub use unfold::*;

#[derive(Default)]
pub struct RewriteList {
    unfoldList: Rc<RefCell<UnfoldList>>,
    constrRewriteList: Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    functionalityComponentsList: Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    definedList: Rc<RefCell<BTreeSet<CHC>>>,
    newDefineMap: Rc<RefCell<BTreeMap<FoldPattern, AppliedId>>>,
}

fn getAnyAndChildren(appId: &AppliedId, eg: &CHCEGraph) -> OrderVec<AppliedIdOrStar> {
    let appId = &eg.find_applied_id(appId);
    let n = eg.enodes_applied(appId).first().unwrap().clone();
    if let CHC::And(andChildren) = n {
        return andChildren;
    };

    if let CHC::True() = n {
        return vec![].into();
    };

    panic!();
}

fn getVarAppId(s: Slot, vt: VarType, eg: &mut CHCEGraph) -> AppliedId {
    match vt {
        VarType::Int => eg.add(CHC::IntType(s)),
        VarType::Node => eg.add(CHC::NodeType(s)),
        VarType::Unknown => {
            todo!()
        }
        VarType::List => eg.add(CHC::ListType(s)),
    }
}

#[macro_export]
macro_rules! checkVarType {
    ($appId: expr, $eg: expr) => {
        if CHECKS {
            let eclassData = $eg.analysis_data($appId.id);
            if $eg.find_applied_id($appId).len() != 0 && eclassData.varTypes().len() == 0 {
                error!("egraph {:?}", $eg);
                error!("varTypes len 0");
                error!("appId {:?}", $appId);
                error!("appId find {:?}", $eg.find_applied_id($appId));
                error!("eclass {:?}", $eg.eclass($appId.id).unwrap());
                assert!(eclassData.varTypes().len() > 0);
            }
        }
    };
}

// it is not always the case that all variables in the head will appear in the body
// eg // left-drop(x,y,z) ← y=leaf, z=leaf

// it is possible that no variables in the head appears in the body at all
// eg
// unfold new(x) <- leafDrop(x, y, z) with left-drop(x,y,z) ← y=leaf, z=leaf
// we get new(x) <- y=leaf, z=leaf, which is true for all x

// only check if one of them appear
#[macro_export]
macro_rules! checkNewENode {
    ($enode: expr, $eg: expr) => {
        if CHECKS {
            let (syntax, cond, children) = match &$enode {
                CHC::New(syntax, cond, children) => (syntax, cond, children),
                _ => panic!(),
            };

            let mut found = false;
            for s in syntax.m.values_set() {
                if cond.m.values_set().contains(&s) {
                    found = true;
                    continue;
                }

                for child in children.iter() {
                    if child.getAppliedId().m.values_set().contains(&s) {
                        found = true;
                        break;
                    }
                }
            }

            if !found && syntax.m.values_set().len() != 0 {
                warn!(
                    "alert enode, head var not in body = {:?}",
                    $enode.weak_shape().0
                );
            }

            getAllVarTypesOfENode(&$enode, $eg);
        }
    };
}

#[macro_export]
macro_rules! checkNewENodeComponent {
    ($syntax:expr, $cond:expr, $children:expr) => {
        let mut found = false;
        for s in $syntax.m.values_set() {
            for condChild in $cond {
                if condChild.getAppliedId().m.values_set().contains(&s) {
                    found = true;
                    continue;
                }
            }

            for child in $children {
                if child.getAppliedId().m.values_set().contains(&s) {
                    found = true;
                    break;
                }
            }
        }
        if !found && $syntax.m.values_set().len() != 0 {
            warn!("alert var in head not not in body");
            // warn!(
            //     "syntax = {:?}, cond = {:?}, children = {:?}",
            //     $syntax, $cond, $children
            // );
        }
    };
}

fn dedupMaintainOrder<T: Eq + std::hash::Hash + Clone>(data: Vec<T>) -> Vec<T> {
    let mut seen = HashSet::new();
    data.into_iter()
        .filter(|item| seen.insert(item.clone()))
        .collect()
}

#[derive(Debug, Clone)]
pub struct RewriteOption {
    pub doFolding: bool,
    pub doConstraintRewrite: bool,
    pub doADTDefine: bool,
    pub doPairingDefine: bool,
}

#[derive(Debug, Clone)]
pub struct ConstrRewriteComponent {
    constrAppId: AppliedId,
    constrENode: CHC,
    newENodeAppId: AppliedId,
    newENode: CHC,
    tag: String,
}

type FoldPattern = Vec<AppliedIdOrStar>;

fn compareAppIdOnInterface(a: &AppliedId, b: &AppliedId, itf: &VecSet<[Slot; 8]>) -> bool {
    if a.id != b.id {
        return false;
    }

    if a.m.len() != b.m.len() {
        return false;
    }

    for (i, ra) in a.m.map.iter().enumerate() {
        let rb = b.m.map[i];
        if itf.contains(&ra.1) || itf.contains(&rb.1) {
            if ra.1 != rb.1 {
                return false;
            }
        }
    }

    true
}

fn functionalityTransformation(
    constrRewriteList: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    functionalityComponentsList: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
) -> CHCRewrite {
    debug!("doing functionalityTransformation");
    let searcher = Box::new(move |eg: &CHCEGraph| -> () {});

    let functionalityComponentsListClone = Rc::clone(&functionalityComponentsList);
    let constrRewriteListClone = Rc::clone(&constrRewriteList);
    let applier = Box::new(move |_: (), eg: &mut CHCEGraph| {
        for components in Rc::clone(&functionalityComponentsListClone).borrow().iter() {
            let ConstrRewriteComponent {
                constrAppId,
                constrENode,
                newENodeAppId,
                newENode,
                tag,
            } = components;

            checkNewENode!(newENode, eg);

            let CHC::New(syntax, andAppId, unfoldedChildren) = newENode.clone() else {
                panic!();
            };

            let CHC::And(andChildren) = constrENode else {
                panic!();
            };

            // input to output mapping
            // (eclassId, inputSlots) -> Vec<(outputSlots, childIdx)>
            // one input can mapped to many outputs
            // those outputs must be equal
            let mut inputToOutputMapping: BTreeMap<(Id, Vec<Slot>), Vec<(Vec<Slot>, usize)>> =
                BTreeMap::default();
            for (childIdx, c) in unfoldedChildren.iter().enumerate() {
                let AppliedIdOrStar::AppliedId(AppliedId { id, m }) = c else {
                    panic!();
                };

                let childrenData = eg.analysis_data(*id);
                if !childrenData.functionalInfo.functional {
                    continue;
                }

                let outputIdx: BTreeSet<usize> = childrenData
                    .functionalInfo
                    .outputIdx
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<usize>>();

                let maxOutputIdx = *outputIdx.iter().max().unwrap();
                let mut inputVars = vec![];
                let mut outputVars = vec![];
                for (i, s) in m.values_vec().iter().enumerate() {
                    assert!(i <= maxOutputIdx);

                    if outputIdx.contains(&i) {
                        outputVars.push(s.clone());
                    } else {
                        inputVars.push(s.clone());
                    }
                }

                inputToOutputMapping
                    .entry((*id, inputVars))
                    .or_insert(vec![])
                    .push((outputVars, childIdx));
            }
            let mut newAndChildren: OrderVec<AppliedIdOrStar> = andChildren.clone();
            let mut filterOutChildIdx = BTreeSet::new();

            // let getVarType = |ofSlot: Slot, appId: AppliedId, egraph: &CHCEGraph| {
            //     // let varTypes = &egraph.analysis_data(appId.id).varTypes;
            //     // TODO: optimize here
            //     let varTypes = getAllVarTypesInEClass(appId.id, egraph);
            //     let fromSlot = appId.m.inverse()[ofSlot];
            //     let res = varTypes.get(&fromSlot);
            //     if res.is_none() {
            //         error!("eclass {:?}", egraph.eclass(appId.id).unwrap());
            //         error!("varTypes {varTypes:?}");
            //         error!("fromSlot {fromSlot}");
            //         error!("ofSlot {ofSlot}");
            //         error!("appId {appId:?}");
            //         assert!(res.is_some());
            //     }
            //     res.unwrap().clone()
            // };

            let varTypes = getAllVarTypesOfENode(newENode, eg);

            for (outputSetsAndChildIdx) in inputToOutputMapping.values() {
                if outputSetsAndChildIdx.len() == 1 {
                    continue;
                }

                let (firstOutputGroup, firstChildIdx) = &outputSetsAndChildIdx[0];
                let outputLen = firstOutputGroup.len();
                for (outputGroup, childIdx) in &outputSetsAndChildIdx[1..] {
                    assert!(outputLen == outputGroup.len());

                    for i in 0..outputLen {
                        // let firstVarType = getVarType(
                        //     firstOutputGroup[i],
                        //     unfoldedChildren[*firstChildIdx].getAppliedId(),
                        //     eg,
                        // );
                        let firstVarType = varTypes.get(&firstOutputGroup[i]).unwrap().clone();
                        let firstGroupVar = getVarAppId(firstOutputGroup[i], firstVarType, eg);
                        // let varType = getVarType(
                        //     outputGroup[i],
                        //     unfoldedChildren[*childIdx].getAppliedId(),
                        //     eg,
                        // );
                        let varType = varTypes.get(&outputGroup[i]).unwrap().clone();
                        let var = getVarAppId(outputGroup[i], varType, eg);

                        let eqId = eg.add(CHC::Eq(firstGroupVar, var));
                        newAndChildren.push(AppliedIdOrStar::AppliedId(eqId));
                    }

                    filterOutChildIdx.insert(*childIdx);
                }
            }

            if filterOutChildIdx.len() == 0 {
                continue;
            }

            let mut newUnfoldedChildren: OrderVec<AppliedIdOrStar> = unfoldedChildren
                .iter()
                .enumerate()
                .filter(|(i, _)| !filterOutChildIdx.contains(i))
                .map(|(_, c)| c.clone())
                .collect();

            let (updatedNewENode, newAnd, newAndAppId) =
                sortNewENode2(&syntax, &newAndChildren, &newUnfoldedChildren, eg);
            let updatedNewENodeAppId = eg.add(updatedNewENode.clone());
            checkVarType!(&updatedNewENodeAppId, eg);

            checkNewENode!(updatedNewENode, eg);

            constrRewriteListClone
                .clone()
                .borrow_mut()
                .push(ConstrRewriteComponent {
                    constrAppId: newAndAppId.clone(),
                    constrENode: newAnd.clone(),
                    newENodeAppId: updatedNewENodeAppId.clone(),
                    newENode: updatedNewENode.clone(),
                    tag: "from_functionalityTransformation".to_owned(),
                });

            eg.union_justified(
                &newENodeAppId,
                &updatedNewENodeAppId,
                Some("functionalityTransformation".to_owned()),
            );
        }

        functionalityComponentsListClone.borrow_mut().clear();
    });

    debug!("done functionalityTransformation");
    RewriteT {
        name: "functionalityTransformation".to_owned(),
        searcher: searcher,
        applier: applier,
    }
    .into()
}

// TODO: caching of processed node here?
// TODO: this function takes a long time
// expand eq rewrite, X = Y, X = Z -> X = Y, X = Z, Y = Z
// expand eq rewrite, X = node(a, l, r), Y = node(a, l, r) -> X = Y, X = node(a, l, r), Y = node(a, l, r)
pub fn expandEqRewrite(
    constrAppId: &AppliedId,
    constrENode: &CHC,
    originalNewENodeAppId: &AppliedId,
    originalNewENode: &CHC,
    eg: &mut CHCEGraph,
) -> CHC {
    debug!("doing expandEqRewrite");
    let CHC::And(andChildren) = constrENode else {
        panic!();
    };

    // unionfind: a set of applied ids
    // how to do this?

    let mut uf = HashUnionFind::new(vec![]);

    let mut eqCount = 0;
    for andChild in andChildren.iter() {
        let AppliedIdOrStar::AppliedId(andChild) = andChild else {
            panic!();
        };

        // get the children of eq in these eclasses
        let enodes = eg.enodes_applied(&andChild);
        for n in enodes {
            let CHC::Eq(eqChild1, eqChild2) = n else {
                continue;
            };

            uf.unionE(&eqChild1, &eqChild2);
        }
    }

    let mut groups = uf.buildGroups();
    let mut newConstraintChildren: BTreeSet<AppliedIdOrStar> = BTreeSet::new();
    newConstraintChildren.extend(andChildren.clone());
    let oldLen = newConstraintChildren.len();

    for group in groups.iter_mut() {
        group.sort();
        for i in 0..group.len() {
            for j in i + 1..group.len() {
                if group[i] == group[j] {
                    continue;
                }

                let eqChild = CHC::Eq(group[i].clone(), group[j].clone());
                let eqChildAppId = eg.add(eqChild);
                checkVarType!(&eqChildAppId, eg);
                newConstraintChildren.insert(AppliedIdOrStar::AppliedId(eqChildAppId));
            }
        }
    }

    if newConstraintChildren.len() == oldLen {
        return constrENode.clone();
    }

    let CHC::New(syntax, _, newENodeChildren) = originalNewENode.clone() else {
        panic!();
    };

    let newConstraintChildren: OrderVec<AppliedIdOrStar> =
        newConstraintChildren.into_iter().collect();

    let (_, newConstraint, newConstraintAppId) =
        sortNewENode2(&syntax, &newConstraintChildren, &newENodeChildren, eg);

    checkVarType!(&newConstraintAppId, eg);
    eg.analysis_data_mut(newConstraintAppId.id)
        .predNames
        .insert(format!(
            "expandEqRewrite_{}_{}",
            constrAppId.id, originalNewENodeAppId.id
        ));

    eg.union_justified(
        constrAppId,
        &newConstraintAppId,
        Some("expandEq".to_owned()),
    );

    debug!("done expandEqRewrite");
    return newConstraint;
}

// TODO: this function is taking a long time
// constructor eq rewrite, node(x, l, r) = node(x', l', r') -> x = x', l = l', r = r'
pub fn constructorEqRewrite(
    constrAppId: &AppliedId,
    constrENode: &CHC,
    originalNewENodeAppId: &AppliedId,
    originalNewENode: &CHC,
    eg: &mut CHCEGraph,
) -> CHC {
    debug!("doing constructorEqRewrite");
    let constrAppId = eg.find_applied_id(constrAppId);
    let constrENode = eg.find_enode(constrENode);
    let CHC::And(andChildrenOrig) = constrENode else {
        panic!();
    };

    let mut andChildren: BTreeSet<AppliedIdOrStar> = BTreeSet::new();
    andChildren.extend(andChildrenOrig.clone());
    for child in andChildrenOrig {
        let AppliedIdOrStar::AppliedId(child) = child else {
            panic!();
        };

        // TODO: change from enodes_applied to static iterator
        let childENodes = eg.enodes_applied(&child);
        for eqNode in childENodes {
            let CHC::Eq(eqChild1, eqChild2) = eqNode else {
                continue;
            };

            let mut nodeFromChild1 = vec![];
            let binodeNodeVec = eg.enodes_applied(&eqChild1);
            for binodeNode in binodeNodeVec {
                let CHC::BiNode(val, l, r) = binodeNode else {
                    continue;
                };
                nodeFromChild1.push((val, l, r));
            }

            let mut nodeFromChild2 = vec![];
            let binodeNodeVec2 = eg.enodes_applied(&eqChild2);
            for binodeNode in binodeNodeVec2 {
                let CHC::BiNode(val, l, r) = binodeNode else {
                    continue;
                };
                nodeFromChild2.push((val, l, r));
            }

            for (val, l, r) in nodeFromChild1 {
                for (val2, l2, r2) in nodeFromChild2.clone() {
                    if val != val2 {
                        let newEqAppId = eg.add(CHC::Eq(val.clone(), val2));
                        checkVarType!(&newEqAppId, eg);
                        andChildren.insert(AppliedIdOrStar::AppliedId(newEqAppId));
                    }

                    if l != l2 {
                        let newEqAppId = eg.add(CHC::Eq(l.clone(), l2));
                        checkVarType!(&newEqAppId, eg);
                        andChildren.insert(AppliedIdOrStar::AppliedId(newEqAppId));
                    }

                    if r != r2 {
                        let newEqAppId = eg.add(CHC::Eq(r.clone(), r2));
                        checkVarType!(&newEqAppId, eg);
                        andChildren.insert(AppliedIdOrStar::AppliedId(newEqAppId));
                    }
                }
            }
        }
    }

    let CHC::New(syntax, _, newENodeChildren) = originalNewENode.clone() else {
        panic!();
    };

    let (_, newConstraint, newConstraintAppId) = sortNewENode2(
        &syntax,
        &andChildren.into_iter().collect(),
        &newENodeChildren,
        eg,
    );

    eg.analysis_data_mut(newConstraintAppId.id)
        .predNames
        .insert(format!(
            "constructorEqRewrite_fromConstr_{}_fromNewENode_{}",
            constrAppId.id, originalNewENodeAppId.id
        ));

    checkVarType!(&newConstraintAppId, eg);
    eg.union_justified(
        &constrAppId,
        &newConstraintAppId,
        Some("constructorEqRewrite".to_owned()),
    );

    debug!("done constructorEqRewrite");
    newConstraint
}

pub fn getEqMapping(
    andChildrenOrig: &OrderVec<AppliedIdOrStar>,
    headVars: &SmallHashSet<Slot>,
    eg: &mut CHCEGraph,
) -> SlotMap {
    let mut uf: HashUnionFind<Slot> = HashUnionFind::new(vec![]);
    for child in andChildrenOrig.iter() {
        let AppliedIdOrStar::AppliedId(child) = child else {
            panic!();
        };

        let eqNodeVec = eg.enodes_applied(&child);
        for eqNode in eqNodeVec {
            let CHC::Eq(eqChild1, eqChild2) = eqNode else {
                continue;
            };

            let mut vt = None;

            let mut leftSideSlots = vec![];
            let singleNodeVec = eg.enodes_applied(&eqChild1);
            for singleNode in singleNodeVec {
                match singleNode {
                    CHC::NodeType(s) => {
                        leftSideSlots.push(s);
                        vt = Some(VarType::Node);
                    }
                    CHC::IntType(s) => {
                        leftSideSlots.push(s);
                        vt = Some(VarType::Int);
                    }
                    _ => continue,
                }
            }

            if leftSideSlots.len() == 0 {
                continue;
            }

            let mut rightSideSlots = vec![];
            let singleNodeVec = eg.enodes_applied(&eqChild2);
            for singleNode in singleNodeVec {
                match singleNode {
                    CHC::NodeType(s) => {
                        rightSideSlots.push(s);
                        assert!(vt.unwrap() == VarType::Node);
                    }
                    CHC::IntType(s) => {
                        rightSideSlots.push(s);
                        assert!(vt.unwrap() == VarType::Int);
                    }
                    _ => continue,
                }
            }

            if rightSideSlots.len() == 0 {
                continue;
            }

            // all map to leftSideSlots[0]
            for l in leftSideSlots.iter() {
                let k1 = uf.findOrAddE(l);
                let k2 = uf.findOrAddE(&leftSideSlots[0]);
                uf.union(k1, k2);
            }
            for r in rightSideSlots.iter() {
                let k1 = uf.findOrAddE(r);
                let k2 = uf.findOrAddE(&leftSideSlots[0]);
                uf.union(k1, k2);
            }
        }
    }

    let mut eqMapping = SlotMap::default();

    let groups = uf.buildGroups();
    for group in groups.iter() {
        let mut mapTo = None;

        // if there is a head var, then mapTo is the head var
        for s in group.iter() {
            if headVars.contains(s) {
                mapTo = Some(s.clone());
                break;
            }
        }

        // else mapTo is the first var in the group
        if mapTo.is_none() {
            mapTo = Some(group[0].clone());
        }

        let mut mapFrom = vec![];

        for s in group.iter() {
            // dont map head vars
            if headVars.contains(s) {
                continue;
            }

            mapFrom.push(*s);
        }

        if mapTo.is_none() {
            continue;
        }

        for s in mapFrom.iter() {
            eqMapping.insert(s.clone(), mapTo.unwrap());
        }
    }

    eqMapping
}

fn newEClassFromEqMapping(
    originalEClass: &AppliedId,
    eqMapping: &SlotMap,
    eg: &mut CHCEGraph,
) -> AppliedId {
    let mut updatedChild: Option<AppliedId> = None;
    let mut hasRewrite = false;
    for s in originalEClass.slots() {
        if eqMapping.contains_key(s) {
            hasRewrite = true;
            break;
        }
    }
    if !hasRewrite {
        return originalEClass.clone();
    }

    let childENodeVec = eg.enodes_applied(originalEClass);
    for childENode in childENodeVec {
        let updatedChildENode = childENode.apply_slotmap_partial(&eqMapping);
        // TODO: do we need speedup here?
        // TODO: what's the effected of this statement?
        let lookupRes = eg.lookup(&updatedChildENode);
        if lookupRes.is_some() {
            updatedChild = lookupRes;
            break;
        }

        let newUpdatedChild = eg.add(updatedChildENode);
        // if lookupRes.is_some() {
        //     assert!(lookupRes.unwrap() == newUpdatedChild);
        // }

        if !updatedChild.is_none() {
            eg.union_justified(
                &updatedChild.clone().unwrap(),
                &newUpdatedChild,
                Some("copy-child".to_owned()),
            );
        }

        updatedChild = Some(newUpdatedChild);
    }

    updatedChild.unwrap()
}

pub fn rewriteConstraintFromEqMapping(
    andChildrenOrig: &OrderVec<AppliedIdOrStar>,
    eqMapping: &SlotMap,
    eg: &mut CHCEGraph,
) -> OrderVec<AppliedIdOrStar> {
    let mut updatedConstrChildren = vec![];
    // apply rewrite from equivalent and check for any self equal enodes i.e. node(a, l, r) = node(a, l, r)
    for child in andChildrenOrig.iter() {
        let AppliedIdOrStar::AppliedId(child) = child else {
            panic!();
        };

        let updatedChild = newEClassFromEqMapping(child, &eqMapping, eg);

        let mut skip = false;
        let selfEqENodeVec = eg.enodes_applied(&updatedChild);
        for selfEqENode in selfEqENodeVec {
            match selfEqENode {
                CHC::Eq(left, right) => {
                    if left == right {
                        skip = true;
                        break;
                    }
                }
                CHC::True() => {
                    skip = true;
                    break;
                }
                _ => {}
            }
        }

        if skip {
            let trueId = eg.add(CHC::True());
            eg.union_justified(&trueId, &updatedChild, Some("selfEq".to_owned()));

            continue;
        }

        updatedConstrChildren.push(AppliedIdOrStar::AppliedId(updatedChild));
    }

    updatedConstrChildren.into()
}

fn rewriteChildrenFromEqMapping(
    children: &OrderVec<AppliedIdOrStar>,
    eqMapping: &SlotMap,
    eg: &mut CHCEGraph,
) -> OrderVec<AppliedIdOrStar> {
    let mut updatedChildren = vec![];
    for child in children.iter() {
        let AppliedIdOrStar::AppliedId(child) = child else {
            panic!();
        };

        let mut updatedChild = newEClassFromEqMapping(child, eqMapping, eg);
        updatedChildren.push(AppliedIdOrStar::AppliedId(updatedChild));
    }

    updatedChildren.into()
}

// a = a1, l = l1, r = r1, t = node(a, l, r), t = node(a1, l1, l1), node(a, l, r) = node(a1, l1, r1) -> a = a1, l = l1, r = r1, t = node(a, l, r)
// deduplicate enode calls a = a1, P(a, z), P(a1, z) -> a = a1, P(a, z)
pub fn dedupFromEqRewrite(
    constrAppId: &AppliedId,
    constrENode: &CHC,
    newENodeAppId: &AppliedId,
    newENode: &CHC,
    eg: &mut CHCEGraph,
) -> (CHC, CHC) {
    debug!("doing dedupFromEqRewrite");
    let constrAppId = eg.find_applied_id(constrAppId);
    let constrENode = eg.find_enode(constrENode);
    let CHC::And(andChildrenOrig) = constrENode.clone() else {
        panic!();
    };

    let CHC::New(syntax, _, newChildren) = &newENode else {
        panic!();
    };

    // get eqMapping
    let eqMapping = getEqMapping(&andChildrenOrig, &syntax.slots(), eg);

    // should not rewrite head variables into something else
    for s in syntax.slots() {
        assert!(!eqMapping.contains_key(s));
    }
    let updatedConstrChildren = rewriteConstraintFromEqMapping(&andChildrenOrig, &eqMapping, eg);

    // note: cannot union with the original constraint because some interface
    // might be dropped after the transformation and we dont want that

    let updatedNewChildren = rewriteChildrenFromEqMapping(newChildren, &eqMapping, eg);

    let (updatedNew, newConstraint, newConstraintAppId) =
        sortNewENode2(syntax, &updatedConstrChildren, &updatedNewChildren, eg);
    eg.analysis_data_mut(newConstraintAppId.id)
        .predNames
        .insert(format!(
            "dedupFromEqRewrite_fromConstr_{}_fromNewENode_{}",
            constrAppId.id, newENodeAppId.id
        ));

    let updatedNewAppId = eg.add(updatedNew.clone());

    eg.union_justified(
        &newENodeAppId,
        &updatedNewAppId,
        Some("dedupFromEqRewrite".to_owned()),
    );

    debug!("done dedupFromEqRewrite");
    (newConstraint, updatedNew)
}

fn constraintRewrite(
    constrRewriteList: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    functionalityComponentsList: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
) -> CHCRewrite {
    let constrRewriteListCopy = Rc::clone(constrRewriteList);
    let functionalityComponentsListCopy = Rc::clone(functionalityComponentsList);
    let searcher = Box::new(move |eg: &CHCEGraph| -> () {});
    let applier = Box::new(move |_: (), eg: &mut CHCEGraph| {
        for constrRewriteComponent in Rc::clone(&constrRewriteListCopy).borrow().iter() {
            let ConstrRewriteComponent {
                constrAppId,
                constrENode,
                newENodeAppId,
                newENode,
                tag,
            } = constrRewriteComponent;

            checkNewENode!(newENode, eg);

            // expand eq rewrite, X = Y, X = Z -> X = Y, X = Z, Y = Z
            // expand eq rewrite, X = node(a, l, r), Y = node(a, l, r) -> X = Y, X = node(a, l, r), Y = node(a, l, r)
            let constrENode =
                expandEqRewrite(constrAppId, constrENode, newENodeAppId, newENode, eg);

            // constructor eq rewrite, node(x, l, r) = node(x', l', r') -> x = x', l = l', r = r'
            let constrENode =
                constructorEqRewrite(constrAppId, &constrENode, newENodeAppId, newENode, eg);

            // deduplicate constraint a = a2, a = a1, l = l1, r = r1, t = node(a, l, r), t = node(a1, l1, r1)
            // -> a = a, l = l, r = r, t = node(a, l, r), t = node(a, l, r)
            // -> t = node(a, l, r)
            // deduplicate predicate calls a = a1, P(a, z), P(a1, z) -> P(a, z)
            let (newConstraint, updatedNewENode) =
                dedupFromEqRewrite(constrAppId, &constrENode, newENodeAppId, newENode, eg);

            checkNewENode!(updatedNewENode, eg);

            // TODO: only push if new children is effected
            functionalityComponentsListCopy
                .clone()
                .borrow_mut()
                .push(ConstrRewriteComponent {
                    constrAppId: constrAppId.clone(),
                    constrENode: newConstraint.clone(),
                    newENodeAppId: newENodeAppId.clone(),
                    newENode: updatedNewENode.clone(),
                    tag: "functionalityTransformation".to_owned(),
                });
        }

        constrRewriteListCopy.borrow_mut().clear();
    });
    RewriteT {
        name: "constraintRewrite".to_owned(),
        searcher: searcher,
        applier: applier,
    }
    .into()
}

// TODO: change this to sort by nauty-trace
fn createSortedDefinedNewENode(
    syntaxVars: &Vec<Slot>,
    children: &OrderVec<AppliedIdOrStar>,
    varTypes: &BTreeMap<Slot, VarType>,
    eg: &mut CHCEGraph,
) -> (AppliedId, CHC, SlotMap) {
    let sortedChildren = sortAppId(
        &children
            .iter()
            .map(|x| x.getAppliedId())
            .collect::<Vec<_>>(),
        true,
    );
    // $0 -> $f
    let (_, map) = weakShapeAppIds(&sortedChildren);
    let mapInverse = map.inverse();
    let mut syntaxVars: Vec<_> = syntaxVars.into_iter().map(|s| mapInverse[*s]).collect();
    syntaxVars.sort();
    let syntaxVars: Vec<_> = syntaxVars.into_iter().map(|s| map[s]).collect();

    let syntaxAppId = {
        let children = syntaxVars
            .into_iter()
            .map(|s| getVarAppId(s, varTypes[&s].clone(), eg))
            .collect::<Vec<_>>();
        let syntaxENode = CHC::PredSyntax(children.into());
        eg.add(syntaxENode)
    };

    let cond = eg.add(CHC::And(vec![].into()));

    (
        syntaxAppId.clone(),
        CHC::New(
            syntaxAppId,
            cond,
            sortedChildren
                .iter()
                .map(|x| AppliedIdOrStar::AppliedId(x.clone()))
                .collect(),
        ),
        map,
    )
}

pub fn sortNewENode1(
    syntaxAppId: &AppliedId,
    condAppId: &AppliedId,
    predicateChildren: &Vec<AppliedIdOrStar>,
    eg: &mut CHCEGraph,
) -> CHC {
    let mut aggrAppId: Vec<_> = predicateChildren.iter().map(|a| a.getAppliedId()).collect();
    aggrAppId.push(condAppId.clone());
    aggrAppId.push(syntaxAppId.clone());
    let aggrAppId = sortAppId(&aggrAppId, true);

    let updatedChildren: Vec<_> = aggrAppId
        .into_iter()
        .filter(|x| x != syntaxAppId && x != condAppId)
        .map(|x| AppliedIdOrStar::AppliedId(x))
        .collect();

    CHC::New(
        syntaxAppId.clone(),
        condAppId.clone(),
        updatedChildren.into(),
    )
}

pub fn sortNewENode2(
    syntaxAppId: &AppliedId,
    condChildren: &OrderVec<AppliedIdOrStar>,
    predicateChildren: &OrderVec<AppliedIdOrStar>,
    eg: &mut CHCEGraph,
) -> (CHC, CHC, AppliedId) {
    debug!("doing sortNewENode2");
    let mut aggrAppId: Vec<_> = predicateChildren.iter().map(|a| a.getAppliedId()).collect();
    aggrAppId.extend(condChildren.iter().map(|a| a.getAppliedId()));
    aggrAppId.push(syntaxAppId.clone());
    let aggrAppId = sortAppId(&aggrAppId, true);

    let condChildrenSet = BTreeSet::from_iter(condChildren.iter().map(|a| a.getAppliedId()));

    let sortedPredicateChildren: Vec<_> = aggrAppId
        .iter()
        .filter(|x| *x != syntaxAppId && !condChildrenSet.contains(x))
        .map(|x| AppliedIdOrStar::AppliedId(x.clone()))
        .collect();

    let sortedCondChildren: Vec<_> = aggrAppId
        .into_iter()
        .filter(|x| x != syntaxAppId && condChildrenSet.contains(x))
        .map(|x| AppliedIdOrStar::AppliedId(x))
        .collect();

    let condENode = CHC::And(sortedCondChildren.clone().into());
    let condAppId = eg.add(condENode.clone());

    trace!("add condENode {condENode:?} to condAppId {condAppId:?}");
    trace!("result eclass {:?}", eg.eclass(condAppId.id).unwrap());

    if CHECKS {
        checkDedup(condAppId.id, &sortedCondChildren.into()).unwrap();
    }

    debug!("done sortNewENode2");
    (
        CHC::New(
            syntaxAppId.clone(),
            condAppId.clone(),
            sortedPredicateChildren.into(),
        ),
        condENode,
        condAppId,
    )
}

struct DefineInfo {
    syntax: Vec<Slot>,
    newBody: Vec<AppliedId>,
    positions: Vec<usize>,
    tag: String,
}

fn define(
    origNewENode: &CHC,
    mergeVarTypes: &BTreeMap<Slot, VarType>,
    options: &RewriteOption,
    eclassId: Id,
    eg: &CHCEGraph,
    syntaxAndNewBody: &mut Vec<DefineInfo>,
) {
    // ADT
    let CHC::New(origSyntaxAppId, origConstrAppId, childAppIds) = &origNewENode else {
        panic!();
    };

    if options.doADTDefine {
        let mut varToChildIdx: BTreeMap<Slot, Vec<usize>> = BTreeMap::default();
        for idx in 0..childAppIds.len() {
            let appId = childAppIds[idx].getAppliedId();
            for s in appId.slots() {
                varToChildIdx.entry(s).or_insert(vec![]).push(idx);
            }
        }

        let mut blockUnionfind: QuickUnionUf<UnionBySize> =
            QuickUnionUf::<UnionBySize>::new(childAppIds.len());
        let mut hasNonBasicVar = vec![false; childAppIds.len()];

        for (var, childrenIndx) in &varToChildIdx {
            if isNonBasicVar(&mergeVarTypes[var]) {
                let leader = childrenIndx.first().unwrap();
                for next in childrenIndx {
                    blockUnionfind.union(*leader, *next);
                    hasNonBasicVar[*next] = true;
                }
            }
        }

        // parition into groups, only get the one that contains non-basic var
        let mut groupsByLeader = BTreeMap::<usize, Vec<usize>>::default();
        for i in 0..blockUnionfind.size() {
            if hasNonBasicVar[i] {
                let leader = blockUnionfind.find(i);
                groupsByLeader.entry(leader).or_insert(vec![]).push(i);
            }
        }

        for (_, mut positions) in groupsByLeader {
            positions.sort();

            let mut basicVars: BTreeSet<Slot> = BTreeSet::default();
            for i in &positions {
                let appId = childAppIds[*i].getAppliedId();
                for var in appId.slots() {
                    if !isNonBasicVar(&mergeVarTypes[&var]) {
                        basicVars.insert(var);
                    }
                }
            }
            let basicVars: Vec<_> = basicVars.into_iter().collect();

            // this can happen if a block does not have any basic var
            if basicVars.len() == 0 {
                warn!("basicVars(new define head) is empty");
                // warn!("origNewENode {:?}", origNewENode);
                // warn!("positions {:?}", positions);
            }

            let newBody = positions
                .iter()
                .map(|idx| childAppIds[*idx].getAppliedId())
                .collect::<Vec<_>>();

            syntaxAndNewBody.push(DefineInfo {
                syntax: basicVars,
                newBody,
                positions,
                tag: format!("ADTon{eclassId}"),
            });
        }
    }

    // pairing
    // only support two predicates now
    if options.doPairingDefine {
        for (i, childAppId1) in childAppIds.iter().enumerate() {
            let childAppId1 = childAppId1.getAppliedId();
            for (j, childAppId2) in childAppIds[i + 1..].iter().enumerate() {
                let childAppId2 = childAppId2.getAppliedId();
                let group = vec![i, j];
                let mut syntax = vec![];
                for var in childAppId1.slots() {
                    syntax.push(var);
                }
                for var in childAppId2.slots() {
                    syntax.push(var);
                }
                syntaxAndNewBody.push(DefineInfo {
                    syntax,
                    newBody: vec![childAppId1.clone(), childAppId2.clone()],
                    positions: group,
                    tag: format!(
                        "pairing_{}_with_{}_from_{}",
                        childAppId1.id, childAppId2.id, eclassId
                    ),
                });
            }
        }
    }
}

fn defineUnfoldFold(
    unfoldList: &Rc<RefCell<UnfoldList>>,
    processedDefinedList: &Rc<RefCell<BTreeSet<CHC>>>,
    newDefineMap: &Rc<RefCell<BTreeMap<FoldPattern, AppliedId>>>,
    constrRewriteList: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    options: RewriteOption,
) -> CHCRewrite {
    let processedDefinedListClone = Rc::clone(processedDefinedList);
    let searcher = Box::new(move |eg: &CHCEGraph| -> () {});
    let unfoldListClone = Rc::clone(unfoldList);
    let newDefineMapClone = Rc::clone(newDefineMap);
    let constrRewriteListCopy = Rc::clone(constrRewriteList);
    let applier = Box::new(move |substs: (), eg: &mut CHCEGraph| {
        let ids = eg.ids();
        for eclassId in ids {
            let eclassId = eg.find_id(eclassId);
            let origNewENodeAppId = eg.mk_identity_applied_id(eclassId);

            let enodesList = eg.enodes(origNewENodeAppId.id);
            for origNewENode in enodesList {
                let origENodeShape = origNewENode.weak_shape().0;
                // check if do this already
                let mut processedDefinedListClone = processedDefinedListClone.borrow_mut();
                if processedDefinedListClone.contains(&origENodeShape) {
                    continue;
                }
                processedDefinedListClone.insert(origENodeShape.clone());

                let CHC::New(origSyntaxAppId, origConstrAppId, childAppIds) = &origNewENode else {
                    continue;
                };

                checkNewENode!(origNewENode, eg);

                let mut mergeVarTypes: BTreeMap<Slot, VarType> =
                    getAllVarTypesOfENode(&origNewENode, eg);

                // TODO0: try change to rootData instead of mergeVarTypes
                // aggregate information

                // divide body into blocks
                let mut syntaxAndNewBody: Vec<DefineInfo> = vec![];
                define(
                    &origNewENode,
                    &mergeVarTypes,
                    &options,
                    eclassId,
                    eg,
                    &mut syntaxAndNewBody,
                );

                // for each group/sharing block, define new chc
                // syntax can be in any order
                // newBody can be in any order
                for DefineInfo {
                    syntax,
                    newBody,
                    positions,
                    tag,
                } in syntaxAndNewBody
                {
                    let sortedNewBody: Vec<AppliedIdOrStar> = sortAppId(&newBody, true)
                        .into_iter()
                        .map(|x| AppliedIdOrStar::AppliedId(x))
                        .collect();
                    // 0 -> $f
                    let (sortedToBeFoldShape, map) = weakShapeAppIds(&sortedNewBody);

                    let mut newDefineMapClone = Rc::clone(&newDefineMapClone);
                    let mut newDefineMapClone = newDefineMapClone.borrow_mut();
                    let defineAppId =
                        if let Some(savedFolded) = newDefineMapClone.get(&sortedToBeFoldShape) {
                            trace!("get savedfolded");
                            savedFolded.clone().apply_slotmap(&map)
                        } else {
                            // define
                            let definedENode = {
                                let mapInverse = map.inverse();
                                let mut syntaxVarsNormalized: Vec<_> =
                                    syntax.into_iter().map(|s| mapInverse[s]).collect();
                                // sort according to order in weakshape (ordered by nauty-trace)
                                syntaxVarsNormalized.sort();
                                let syntaxVars: Vec<_> =
                                    syntaxVarsNormalized.into_iter().map(|s| map[s]).collect();

                                let syntaxAppId = {
                                    let children = syntaxVars
                                        .into_iter()
                                        .map(|s| getVarAppId(s, mergeVarTypes[&s].clone(), eg))
                                        .collect::<Vec<_>>();
                                    let syntaxENode = CHC::PredSyntax(children.into());
                                    eg.add(syntaxENode)
                                };

                                let cond = eg.add(CHC::And(vec![].into()));
                                CHC::New(syntaxAppId, cond, sortedNewBody.clone().into())
                            };

                            // unfold
                            let mut composeUnfoldRecipes = vec![];
                            prepareUnfold(
                                0,
                                &vec![].into(),
                                &AppliedId::null(),
                                &AppliedId::null(),
                                &definedENode,
                                &mut composeUnfoldRecipes,
                                eg,
                            );

                            // TODO: it should be more than one
                            let mut newComposeAppIds = vec![];
                            {
                                for composeUnfoldRecipe in composeUnfoldRecipes.into_iter() {
                                    newComposeAppIds.extend(unfoldApplyInternal(
                                        &UnfoldOption {
                                            composeUnfoldRecipe,
                                            createOrMerge: UnfoldOpType::UnfoldCreateOnly,
                                            extraTag: tag.clone(),
                                        },
                                        &unfoldListClone,
                                        &Rc::clone(&constrRewriteListCopy),
                                        eg,
                                    ));
                                }
                            }
                            {

                                // if composeUnfoldReceipt.len() > 1 {
                                //     // printENode(&definedENode, eg);
                                //     // println!("composeUnfoldReceipt {:#?}", composeUnfoldReceipt);
                                //     // assert!(composeUnfoldReceipt.len() == 1);
                                //     warn!("composeUnfoldReceipt len > 1 but also use the first one");
                                //     // warn!("composeUnfoldReceipt {:?}", composeUnfoldReceipt);
                                // }
                                // let newComposeAppIds = unfoldApplyInternal(
                                //     &composeUnfoldReceipt[0],
                                //     &unfoldListClone,
                                //     &Rc::clone(&constrRewriteListCopy),
                                //     UnfoldOpType::UnfoldCreateOnly,
                                //     &tag,
                                //     eg,
                                // );

                                // if (newComposeAppIds.is_empty()) {
                                //     println!("unfold result is empty");
                                //     println!("composeRecipes {:?}");
                                // }
                            }

                            let first = newComposeAppIds.first().unwrap();
                            for newComposeAppId in newComposeAppIds[1..].iter() {
                                eg.union_justified(
                                    first,
                                    newComposeAppId,
                                    Some("define_unfold".to_owned()),
                                );
                            }

                            assert!(unfoldListClone.borrow().len() > 0);

                            let saveAppId = eg.find_applied_id(first).apply_slotmap(&map.inverse());
                            debug!("defineMap {saveAppId:?} <- {sortedToBeFoldShape:?}");
                            newDefineMapClone.insert(sortedToBeFoldShape.into(), saveAppId);

                            eg.find_applied_id(first)
                        };

                    eg.analysis_data_mut(defineAppId.id)
                        .predNames
                        .insert(format!("define_from_{}_{}", origNewENodeAppId.id, tag));

                    // vv folding vv
                    if options.doFolding {
                        let replaceAt = positions.first().unwrap();
                        debug!("sortedToBeFold {sortedNewBody:?}");
                        debug!("fold to {defineAppId:?}");
                        let mut restChildAppIds = vec![];
                        for (idx, c) in childAppIds.iter().enumerate() {
                            if idx == *replaceAt {
                                // TODO: defineAppId must be mapped to originalENode namespace
                                restChildAppIds
                                    .push(AppliedIdOrStar::AppliedId(defineAppId.clone()));
                            }

                            if positions.contains(&idx) {
                                continue;
                            }
                            restChildAppIds.push(c.clone());
                        }
                        debug!("origNewENode {origNewENode:?}");
                        let foldedNewENode = sortNewENode1(
                            origSyntaxAppId,
                            origConstrAppId,
                            &restChildAppIds.into(),
                            eg,
                        );
                        debug!("foldedNewENode {foldedNewENode:?}");
                        let foldedAppId = eg.add(foldedNewENode);
                        eg.analysis_data_mut(foldedAppId.id)
                            .predNames
                            .insert(format!(
                                "folded_{}_with_{}",
                                origNewENodeAppId, defineAppId.id
                            ));
                        eg.union_justified(
                            &origNewENodeAppId,
                            &foldedAppId,
                            Some("fold".to_owned()),
                        );
                    }
                }
            }
        }
    });

    RewriteT {
        name: "define".to_owned(),
        searcher,
        applier,
    }
    .into()
}

fn trueToAnd() -> CHCRewrite {
    let pat = "(true)";
    let outPat = "(and <>)";
    Rewrite::new("trueToAnd", pat, outPat)
}

fn eqSwap() -> CHCRewrite {
    let pat = "(eq ?a ?b)";
    let outPat = "(eq ?b ?a)";
    Rewrite::new("eqSwap", pat, outPat)
}

// TODO: swapping unfold and define creates some error which should not be
pub fn getAllRewrites(rewriteList: RewriteList, options: RewriteOption) -> Vec<CHCRewrite> {
    let RewriteList {
        unfoldList,
        constrRewriteList,
        functionalityComponentsList,
        definedList,
        newDefineMap,
    } = rewriteList;
    // define-fold, unfold
    let mut rewrites = vec![unfold(&unfoldList, &constrRewriteList)];

    // constraint until saturation
    if options.doConstraintRewrite {
        // TODO: can be a while loop?
        rewrites.push(constraintRewrite(
            &constrRewriteList,
            &functionalityComponentsList,
        ));
        rewrites.push(functionalityTransformation(
            &constrRewriteList,
            &functionalityComponentsList,
        ));
        rewrites.push(constraintRewrite(
            &constrRewriteList,
            &functionalityComponentsList,
        ));
        rewrites.push(functionalityTransformation(
            &constrRewriteList,
            &functionalityComponentsList,
        ));
        rewrites.push(constraintRewrite(
            &constrRewriteList,
            &functionalityComponentsList,
        ));
    }

    rewrites.extend([
        defineUnfoldFold(
            &unfoldList,
            &definedList,
            &newDefineMap,
            &constrRewriteList,
            options,
        ),
        trueToAnd(),
        eqSwap(),
    ]);

    rewrites
}
