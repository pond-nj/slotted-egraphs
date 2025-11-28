use super::*;
use crate::*;
use derive_more::derive;
use log::debug;
use std::cell::{Ref, RefCell};
use std::collections::{BTreeSet, HashMap};
use std::f32::consts::E;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};
use tracing_subscriber::filter::combinator::And;
use union_find::{QuickUnionUf, UnionBySize, UnionFind};
use vec_collections::VecSet;

static G_COUNTER: AtomicUsize = AtomicUsize::new(0);

use std::collections::HashSet;

fn getAnyAndChildren(appId: &AppliedId, eg: &CHCEGraph) -> Vec<AppliedIdOrStar> {
    let n = eg.enodes_applied(appId).first().unwrap().clone();
    if let CHC::And(andChildren) = n {
        return andChildren;
    };

    if let CHC::True() = n {
        return vec![];
    };

    panic!();
}

fn checkVarType(appId: &AppliedId, eg: &CHCEGraph) {
    let eclassData = eg.analysis_data(appId.id);
    assert!(eclassData.varTypes.len() != 0);
}

#[derive(Debug, Clone)]
pub struct UnfoldRecipe {
    syntax1: AppliedId,
    mergeAndChildren: Vec<AppliedIdOrStar>,
    unfoldedChildren: Vec<AppliedIdOrStar>,
    new2EClass: AppliedId,
}

#[derive(Debug)]
struct ComposeUnfoldRecipe {
    unfoldRecipe: Vec<Vec<UnfoldRecipe>>,
    exclude: usize,
    compose1Children: Vec<AppliedId>,
    rootId: AppliedId,
    compose2Id: AppliedId,
    comp2Idx: usize,
    new1EClass: AppliedId,
}

#[derive(Debug, Clone)]
pub struct UnfoldListComponent {
    composeAppId: AppliedId,
    composeShape: CHC,
    newEClassAppId: AppliedId,
    newENodeShape: CHC,
}

#[derive(Debug, Clone)]
pub struct ConstrRewriteComponent {
    constrAppId: AppliedId,
    constrENode: CHC,
    newENodeAppId: AppliedId,
    newENode: CHC,
}

impl UnfoldListComponent {
    pub fn find(&self, eg: &CHCEGraph) -> UnfoldListComponent {
        UnfoldListComponent {
            composeAppId: eg.find_applied_id(&self.composeAppId),
            composeShape: eg.find_enode(&self.composeShape),
            newEClassAppId: eg.find_applied_id(&self.newEClassAppId),
            newENodeShape: eg.find_enode(&self.newENodeShape),
        }
    }

    pub fn getShape(&self) -> (UnfoldListComponent, SlotMap) {
        let (composeShape, m) = self.composeShape.weak_shape();

        (
            UnfoldListComponent {
                composeAppId: self.composeAppId.apply_slotmap(&m.inverse()),
                composeShape,
                newEClassAppId: self.newEClassAppId.apply_slotmap(&m.inverse()),
                newENodeShape: self.newENodeShape.clone(),
            },
            m,
        )
    }
}

type UnfoldList = Vec<(UnfoldListComponent)>;
type FunctionalRewriteList = Vec<(CHC, AppliedId)>;

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

fn addToUnfoldList(unfoldList: &Rc<RefCell<UnfoldList>>, toBeUnfolded: UnfoldListComponent) {
    debug!("pusing to unfoldList {toBeUnfolded:#?}");

    let CHC::New(syntax1, cond1, new1Children) = &toBeUnfolded.newENodeShape else {
        panic!();
    };

    if new1Children.len() == 0 {
        debug!("skip toBeUnfolded {toBeUnfolded:#?}");
        return;
    }

    let mut unfoldListCopy = Rc::clone(unfoldList);
    unfoldListCopy.borrow_mut().push(toBeUnfolded);
}

fn doFunctionalityTransformation(
    eg: &mut CHCEGraph,
    origId: &AppliedId,
    syntax: &AppliedId,
    andChildren: &Vec<AppliedIdOrStar>,
    unfoldedChildren: &Vec<AppliedIdOrStar>,
) {
    // input to output mapping
    let mut inputToOutputMapping: BTreeMap<(Vec<Slot>, Id), Vec<(Vec<Slot>, usize)>> =
        BTreeMap::default();
    for (i, c) in unfoldedChildren.iter().enumerate() {
        let AppliedIdOrStar::AppliedId(AppliedId { id, m }) = c else {
            panic!();
        };

        let outputIdx = &eg.analysis_data(*id).functionalInfo.outputIdx;
        let maxOutputIdx = *outputIdx.iter().max().unwrap();
        let mut inputVars = vec![];
        let mut outputVars = vec![];
        for (i, s) in m.values().iter().enumerate() {
            if i > maxOutputIdx {
                break;
            }
            if outputIdx.contains(&i) {
                outputVars.push(s.clone());
            } else {
                inputVars.push(s.clone());
            }
        }

        inputToOutputMapping
            .entry((inputVars, *id))
            .or_insert(vec![])
            .push((outputVars, i));
    }

    let mut newAndChildren: Vec<AppliedIdOrStar> = andChildren.clone();
    let mut filterOutChildIdx = BTreeSet::new();
    for ((inputVars, id), outputSetsAndChildIdx) in inputToOutputMapping {
        if outputSetsAndChildIdx.len() == 1 {
            continue;
        }

        let (firstOutputSet, _) = &outputSetsAndChildIdx[0];
        let outputLen = firstOutputSet.len();
        for (outputSet, childIdx) in &outputSetsAndChildIdx[1..] {
            assert!(outputLen == outputSet.len());
            for i in 0..outputLen {
                let eqExpr: RecExpr<CHC> =
                    RecExpr::parse(&format!("(eq {} {})", firstOutputSet[i], outputSet[i]))
                        .unwrap();
                let eqId = eg.add_expr(eqExpr);
                newAndChildren.push(AppliedIdOrStar::AppliedId(eqId));
            }

            filterOutChildIdx.insert(*childIdx);
        }
    }
    if filterOutChildIdx.len() == 0 {
        return;
    }

    newAndChildren.sort();

    let mut newUnfoldedChildren: Vec<AppliedIdOrStar> = unfoldedChildren
        .into_iter()
        .enumerate()
        .filter(|(i, _)| !filterOutChildIdx.contains(i))
        .map(|(_, c)| c.clone())
        .collect();
    newUnfoldedChildren.sort();

    let newAnd = eg.add(CHC::And(newAndChildren));
    checkVarType(&newAnd, eg);
    // TODO: add data to the newAnd

    let newENode = CHC::New(syntax.clone(), newAnd, newUnfoldedChildren);
    let newENodeId = eg.add(newENode);
    checkVarType(&newENodeId, eg);
    // TODO: add data to the newENode

    eg.union_justified(
        &origId,
        &newENodeId,
        Some("functionalityTransformation".to_owned()),
    );
}

fn unfold(
    unfoldList: &Rc<RefCell<UnfoldList>>,
    constrRewriteList: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    gCounter: &Rc<RefCell<u32>>,
) -> CHCRewrite {
    let unfoldListCopy = Rc::clone(unfoldList);
    let constrRewriteListCopy = Rc::clone(constrRewriteList);
    let gCounterClone = Rc::clone(gCounter);
    let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<ComposeUnfoldRecipe> {
        let mut composeUnfoldReceipt = vec![];

        let oldEgSize = eg.total_number_of_nodes();
        for toBeUnfolded in Rc::clone(&unfoldListCopy).borrow().iter() {
            debug!("unfold: get toBeUnfolded before getShape {toBeUnfolded:#?}");
            let (toBeUnfolded, m) = toBeUnfolded.find(eg).getShape();
            debug!("unfold: get toBeUnfolded {toBeUnfolded:#?}");
            let UnfoldListComponent {
                composeAppId,
                composeShape,
                newEClassAppId,
                newENodeShape,
            } = toBeUnfolded.clone();
            let composeAppId = eg.find_applied_id(&composeAppId);
            let composeAppId = eg.mk_identity_applied_id(composeAppId.id);

            let compose1 = eg.getExactENodeInEGraph(&composeShape);

            // debug!("composeAppId {composeAppId:?}");
            // debug!("compose eclass {:#?}", eg.eclass(composeAppId.id));
            // debug!(
            //     "compose eclass slots {:#?}",
            //     eg.eclass(composeAppId.id).unwrap().slots()
            // );
            // debug!("get compose1 {:?}", compose1);

            let CHC::Compose(compose1Children) = compose1 else {
                panic!();
            };
            let mut compose1Children: Vec<AppliedId> = compose1Children
                .into_iter()
                .map(|appId| {
                    let AppliedIdOrStar::AppliedId(appId) = appId else {
                        panic!();
                    };
                    appId
                })
                .collect();
            compose1Children.sort();
            let composeUnfoldRecipeLenBefore = composeUnfoldReceipt.len();

            // debug!(
            //     "updated newEClassAppId {newEClassAppId:?} -> {}",
            //     eg.find_applied_id(&newEClassAppId)
            // );
            for (i1, new1EClass) in compose1Children.iter().enumerate() {
                if new1EClass.id != eg.find_applied_id(&newEClassAppId).id {
                    debug!("skip new1EClass {:?}", new1EClass);
                    continue;
                }

                let new1 = eg
                    .getExactENodeInEGraph(&newENodeShape)
                    .apply_slotmap_partial(&new1EClass.m);

                let CHC::New(syntax1, cond1, new1Children) = new1.clone() else {
                    panic!();
                };

                let and1Children = getAnyAndChildren(&cond1, eg);
                for (comp2Idx, compose2Id) in new1Children.iter().enumerate() {
                    let compose2Id = compose2Id.getAppliedId();
                    for compose2 in eg.enodes_applied(&compose2Id) {
                        if let CHC::ComposeInit(..) = compose2 {
                            continue;
                        }

                        let CHC::Compose(compose2Children) = compose2 else {
                            panic!();
                        };

                        let mut unfoldedENodesRecipe: Vec<Vec<UnfoldRecipe>> = vec![];
                        for new2EClass in compose2Children.iter() {
                            let new2EClass = new2EClass.getAppliedId();
                            let mut fromThisEClassRecipe: Vec<UnfoldRecipe> = vec![];
                            for new2 in eg.enodes_applied(&new2EClass) {
                                let CHC::New(syntax2, cond2, new2Children) = new2 else {
                                    panic!();
                                };
                                let and2Children = getAnyAndChildren(&cond2, eg);

                                let mut unfoldedChildren = new1Children.clone();
                                unfoldedChildren.remove(comp2Idx);
                                unfoldedChildren.extend(new2Children.clone());

                                // must be sorted first before dedup, dedup only remove consecutive duplicates
                                unfoldedChildren.sort();
                                unfoldedChildren.dedup();

                                let mut mergeAndChildren = and1Children.clone();
                                mergeAndChildren.extend(and2Children);

                                mergeAndChildren.sort();
                                mergeAndChildren.dedup();

                                // prepare for rewrite.
                                // cannot rewrite here because this is searcher only.
                                // separate search and rewrte.
                                fromThisEClassRecipe.push(UnfoldRecipe {
                                    syntax1: syntax1.clone(),
                                    mergeAndChildren,
                                    unfoldedChildren,
                                    new2EClass: new2EClass.clone(),
                                });
                            }
                            unfoldedENodesRecipe.push(fromThisEClassRecipe);
                        }

                        let x = ComposeUnfoldRecipe {
                            unfoldRecipe: unfoldedENodesRecipe,
                            exclude: i1,
                            compose1Children: compose1Children.clone(),
                            rootId: composeAppId.clone(),
                            compose2Id: compose2Id.clone(),
                            comp2Idx,
                            new1EClass: new1EClass.clone(),
                        };

                        debug!("adding unfoldRecipe {x:#?}");
                        debug!("compose1 eclass {:#?}", eg.eclass(composeAppId.id));

                        composeUnfoldReceipt.push(x);
                    }
                }
            }

            if composeUnfoldReceipt.len() == composeUnfoldRecipeLenBefore {
                panic!("skip this recipe");
            }
        }

        debug!("unfold search ret {composeUnfoldReceipt:#?}");
        assert!(eg.total_number_of_nodes() == oldEgSize);
        composeUnfoldReceipt
    });

    let unfoldListCopy2 = Rc::clone(unfoldList);
    let applier = Box::new(
        move |composeRecipes: Vec<ComposeUnfoldRecipe>, eg: &mut CHCEGraph| {
            Rc::clone(&unfoldListCopy2).borrow_mut().clear();
            for composeRecipe in composeRecipes {
                debug!("composeRecipe {composeRecipe:#?}");
                let ComposeUnfoldRecipe {
                    unfoldRecipe,
                    exclude,
                    compose1Children,
                    rootId,
                    compose2Id,
                    comp2Idx,
                    new1EClass,
                } = composeRecipe;
                let mut toBeUnion = vec![];
                // this loops takes a long time, around 1sec per iter
                for unfoldRecipeComb in combination(&unfoldRecipe) {
                    let mut childrenComb = vec![];
                    let mut createdENodes = vec![];
                    let (_, time1) = time(|| {
                        for unfoldRecipe in unfoldRecipeComb {
                            // println!("unfoldRecipe {unfoldRecipe:#?}");
                            let UnfoldRecipe {
                                syntax1,
                                mut mergeAndChildren,
                                mut unfoldedChildren,
                                new2EClass,
                            } = unfoldRecipe;
                            // println!("mergeAndChildren {mergeAndChildren:?}");

                            let mergeAnd = CHC::And(mergeAndChildren.clone());
                            let mergeAndAppId = eg.add(mergeAnd.clone());
                            checkVarType(&mergeAndAppId, eg);

                            eg.analysis_data_mut(mergeAndAppId.id)
                                .predNames
                                .insert(format!(
                                "and_from_unfold_{compose2Id}_{comp2Idx}_in_{new1EClass}_using_{new2EClass}"
                            ));

                            let unfoldedENode = CHC::New(
                                syntax1.clone(),
                                mergeAndAppId.clone(),
                                unfoldedChildren.clone(),
                            );

                            let unfoldedENodeId = eg.add(unfoldedENode.clone());
                            eg.shrink_slots(&unfoldedENodeId, &syntax1.slots(), ());

                            constrRewriteListCopy
                                .borrow_mut()
                                .push(ConstrRewriteComponent {
                                    constrAppId: mergeAndAppId.clone(),
                                    constrENode: mergeAnd,
                                    newENodeAppId: unfoldedENodeId.clone(),
                                    newENode: unfoldedENode.clone(),
                                });

                            checkVarType(&unfoldedENodeId, eg);
                            // doFunctionalityTransformation(
                            //     eg,
                            //     &unfoldedENodeId,
                            //     &syntax1,
                            //     &mergeAndChildren,
                            //     &unfoldedChildren,
                            // );

                            createdENodes.push((unfoldedENodeId.clone(), unfoldedENode.clone()));
                            // debug!("adding unfoldedENode {unfoldedENodeId:?} {unfoldedENode:?}");
                            eg.analysis_data_mut(unfoldedENodeId.id)
                                .predNames
                                .insert(format!(
                                "unfold_{compose2Id}_{comp2Idx}_in_{new1EClass}_using_{new2EClass}"
                            ));
                            childrenComb.push(unfoldedENodeId);
                        }
                    });

                    let (_, time2) = time(|| {
                        let mut unfoldedComposeChildren = compose1Children.clone();
                        unfoldedComposeChildren.remove(exclude);
                        unfoldedComposeChildren.extend(childrenComb);
                        unfoldedComposeChildren.sort();
                        let unfoldedComposeChildren = unfoldedComposeChildren
                            .into_iter()
                            .map(|appId| AppliedIdOrStar::AppliedId(appId.clone()))
                            .collect();
                        let composeENode = CHC::Compose(unfoldedComposeChildren);
                        let unfoldedCompose = eg.add(composeENode.clone());
                        checkVarType(&unfoldedCompose, eg);
                        debug!("adding composeENode {:?} {composeENode:?}", unfoldedCompose);
                        debug!("to be union with {:?}", rootId);
                        toBeUnion.push(unfoldedCompose.clone());
                        eg.union_justified(&rootId, &unfoldedCompose, Some("unfold".to_owned()));

                        for (enodeId, enode) in createdENodes {
                            addToUnfoldList(
                                &unfoldListCopy2,
                                UnfoldListComponent {
                                    composeAppId: unfoldedCompose.clone(),
                                    composeShape: composeENode.clone(),
                                    newEClassAppId: enodeId,
                                    newENodeShape: enode,
                                },
                            );
                        }
                    });
                }

                // for x in toBeUnion {
                //     debug!("union {:?}", eg.eclass(x.id));
                //     debug!("with {:?}", eg.eclass(rootId.id));
                //     eg.union_justified(&rootId, &x, Some("unfold".to_owned()));
                // }
            }
        },
    );

    RewriteT {
        name: "unfold".to_owned(),
        searcher: searcher,
        applier: applier,
    }
    .into()
}

// TODO: caching of processed node here?
fn expandEqRewrite(constrAppId: &AppliedId, constrENode: &CHC, eg: &mut CHCEGraph) -> CHC {
    let CHC::And(andChildren) = constrENode else {
        panic!();
    };

    // unionfind: a set of applied ids
    // how to do this?

    let mut uf = HashUnionFind::new(vec![]);

    let mut eqCount = 0;
    for andChild in andChildren {
        let AppliedIdOrStar::AppliedId(andChild) = andChild else {
            panic!();
        };

        // get the children of eq in these eclasses
        for n in eg.enodes_applied(&andChild) {
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
                checkVarType(&eqChildAppId, eg);
                newConstraintChildren.insert(AppliedIdOrStar::AppliedId(eqChildAppId));
            }
        }
    }
    // TODO: it should be ==
    // but will there be a bug with this?
    if newConstraintChildren.len() == oldLen {
        return constrENode.clone();
    }

    let mut newConstraintChildren: Vec<AppliedIdOrStar> =
        newConstraintChildren.into_iter().collect();
    newConstraintChildren.sort();
    let newConstraint = CHC::And(newConstraintChildren);
    let newConstraintAppId = eg.add(newConstraint.clone());

    if newConstraintAppId.id == constrAppId.id {
        return newConstraint;
    }

    checkVarType(&newConstraintAppId, eg);
    eg.union_justified(
        constrAppId,
        &newConstraintAppId,
        Some("expandEq".to_owned()),
    );

    return newConstraint;
}

fn constructorEqRewrite(constrAppId: &AppliedId, constrENode: &CHC, eg: &mut CHCEGraph) -> CHC {
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

        for eqNode in eg.enodes_applied(&child) {
            let CHC::Eq(eqChild1, eqChild2) = eqNode else {
                continue;
            };

            let mut nodeFromChild1 = vec![];
            for binodeNode in eg.enodes_applied(&eqChild1) {
                let CHC::BiNode(val, l, r) = binodeNode else {
                    continue;
                };
                nodeFromChild1.push((val, l, r));
            }

            let mut nodeFromChild2 = vec![];
            for binodeNode in eg.enodes_applied(&eqChild2) {
                let CHC::BiNode(val, l, r) = binodeNode else {
                    continue;
                };
                nodeFromChild2.push((val, l, r));
            }

            for (val, l, r) in nodeFromChild1 {
                for (val2, l2, r2) in nodeFromChild2.clone() {
                    if val != val2 {
                        let newEqAppId = eg.add(CHC::Eq(val.clone(), val2));
                        checkVarType(&newEqAppId, eg);
                        andChildren.insert(AppliedIdOrStar::AppliedId(newEqAppId));
                    }

                    if l != l2 {
                        let newEqAppId = eg.add(CHC::Eq(l.clone(), l2));
                        checkVarType(&newEqAppId, eg);
                        andChildren.insert(AppliedIdOrStar::AppliedId(newEqAppId));
                    }

                    if r != r2 {
                        let newEqAppId = eg.add(CHC::Eq(r.clone(), r2));
                        checkVarType(&newEqAppId, eg);
                        andChildren.insert(AppliedIdOrStar::AppliedId(newEqAppId));
                    }
                }
            }
        }
    }

    let newConstraint = CHC::And(andChildren.into_iter().collect());
    let newConstraintAppId = eg.add(newConstraint.clone());
    checkVarType(&newConstraintAppId, eg);
    eg.union_justified(
        &constrAppId,
        &newConstraintAppId,
        Some("constructorEqRewrite".to_owned()),
    );

    newConstraint
}

fn getEqMapping(andChildrenOrig: &Vec<AppliedIdOrStar>, eg: &mut CHCEGraph) -> SlotMap {
    let mut eqMapping = SlotMap::default();
    for child in andChildrenOrig.iter() {
        let AppliedIdOrStar::AppliedId(child) = child else {
            panic!();
        };

        for eqNode in eg.enodes_applied(&child) {
            let CHC::Eq(eqChild1, eqChild2) = eqNode else {
                continue;
            };
            // find (eq (node $f658) (node $f659))

            let mut vt = None;

            let mut leftSideSlots = vec![];
            for singleNode in eg.enodes_applied(&eqChild1) {
                match singleNode {
                    CHC::Node(s) => {
                        leftSideSlots.push(s);
                        vt = Some(VarType::Node);
                    }
                    CHC::Int(s) => {
                        leftSideSlots.push(s);
                        vt = Some(VarType::Int);
                    }
                    CHC::Var(s) => {
                        leftSideSlots.push(s);
                        vt = Some(VarType::Unknown);
                    }
                    _ => continue,
                }
            }

            if leftSideSlots.len() == 0 {
                continue;
            }

            let mut rightSideSlots = vec![];
            for singleNode in eg.enodes_applied(&eqChild2) {
                match singleNode {
                    CHC::Node(s) => {
                        rightSideSlots.push(s);
                        assert!(vt.unwrap() == VarType::Node);
                    }
                    CHC::Int(s) => {
                        rightSideSlots.push(s);
                        assert!(vt.unwrap() == VarType::Int);
                    }
                    CHC::Var(s) => {
                        rightSideSlots.push(s);
                        assert!(vt.unwrap() == VarType::Unknown);
                    }
                    _ => continue,
                }
            }

            if rightSideSlots.len() == 0 {
                continue;
            }

            // all map to leftSideSlots[0]
            for l in leftSideSlots.iter() {
                eqMapping.insert(l.clone(), leftSideSlots[0]);
            }
            for r in rightSideSlots {
                eqMapping.insert(r.clone(), leftSideSlots[0]);
            }
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

    for childENode in eg.enodes_applied(originalEClass) {
        let updatedChildENode = childENode.apply_slotmap_partial(&eqMapping);
        // TODO: do we need speedup here, it's not tested
        // TODO: what's the effected of this statement?
        // let lookupRes = eg.lookup(&updatedChildENode);
        // if lookupRes.is_some() {
        //     return lookupRes.unwrap();
        // }

        let newUpdatedChild = eg.add(updatedChildENode);

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

fn rewriteConstraintFromEqMapping(
    andChildrenOrig: &Vec<AppliedIdOrStar>,
    eqMapping: &SlotMap,
    eg: &mut CHCEGraph,
) -> Vec<AppliedIdOrStar> {
    let mut updatedConstrChildren = vec![];
    // apply rewrite from equivalent and check for any self equal enodes i.e. node(a, l, r) = node(a, l, r)
    for child in andChildrenOrig.iter() {
        let AppliedIdOrStar::AppliedId(child) = child else {
            panic!();
        };

        let updatedChild = newEClassFromEqMapping(child, &eqMapping, eg);

        let mut skip = false;
        for selfEqENode in eg.enodes_applied(&updatedChild) {
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

    updatedConstrChildren.sort();
    updatedConstrChildren.dedup();

    updatedConstrChildren
}

fn rewriteChildrenFromEqMapping(
    children: &Vec<AppliedIdOrStar>,
    eqMapping: &SlotMap,
    eg: &mut CHCEGraph,
) -> Vec<AppliedIdOrStar> {
    let mut updatedChildren = vec![];
    for child in children.iter() {
        let AppliedIdOrStar::AppliedId(child) = child else {
            panic!();
        };

        let mut updatedChild = newEClassFromEqMapping(child, eqMapping, eg);
        updatedChildren.push(AppliedIdOrStar::AppliedId(updatedChild));
    }

    updatedChildren.sort();
    updatedChildren.dedup();

    updatedChildren
}

// a = a1, l = l1, r = r1, t = node(a, l, r), t = node(a1, l1, l1), node(a, l, r) = node(a1, l1, r1) -> a = a1, l = l1, r = r1, t = node(a, l, r)
// deduplicate enode calls a = a1, P(a, z), P(a1, z) -> a = a1, P(a, z)
fn dedupFromEqRewrite(
    constrAppId: &AppliedId,
    constrENode: &CHC,
    newENodeAppId: &AppliedId,
    newENode: &CHC,
    eg: &mut CHCEGraph,
) -> CHC {
    let constrAppId = eg.find_applied_id(constrAppId);
    let constrENode = eg.find_enode(constrENode);
    let CHC::And(andChildrenOrig) = constrENode.clone() else {
        panic!();
    };

    // get eqMapping
    let eqMapping = getEqMapping(&andChildrenOrig, eg);
    let updatedConstrChildren = rewriteConstraintFromEqMapping(&andChildrenOrig, &eqMapping, eg);
    let newConstraint = CHC::And(updatedConstrChildren);
    let newConstraintAppId = eg.add(newConstraint.clone());
    // note: cannot union with the original constraint because some interface
    // might be dropped after the transformation and we dont want that
    let newConstraintAppId = eg.add(newConstraint.clone());

    let CHC::New(syntax, _, newChildren) = &newENode else {
        panic!();
    };

    let updatedNewChildren = rewriteChildrenFromEqMapping(newChildren, &eqMapping, eg);
    let updatedNew = CHC::New(syntax.clone(), newConstraintAppId, updatedNewChildren);
    let updatedNewAppId = eg.add(updatedNew.clone());

    eg.union_justified(
        &newENodeAppId,
        &updatedNewAppId,
        Some("dedupFromEqRewrite".to_owned()),
    );

    updatedNew
}

fn constraintRewrite(constrRewriteList: &Rc<RefCell<Vec<ConstrRewriteComponent>>>) -> CHCRewrite {
    let constrRewriteListCopy = Rc::clone(constrRewriteList);
    let searcher = Box::new(move |eg: &CHCEGraph| -> () {});
    let applier = Box::new(move |_: (), eg: &mut CHCEGraph| {
        println!("start constraintRewrite");
        for constrRewriteComponent in Rc::clone(&constrRewriteListCopy).borrow().iter() {
            let ConstrRewriteComponent {
                constrAppId,
                constrENode,
                newENodeAppId,
                newENode,
            } = constrRewriteComponent;

            // expand eq rewrite, X = Y, X = Z -> X = Y, X = Z, Y = Z
            // expand eq rewrite, X = node(a, l, r), Y = node(a, l, r) -> X = Y, X = node(a, l, r), Y = node(a, l, r)
            let constrENode = expandEqRewrite(constrAppId, constrENode, eg);

            // constructor eq rewrite, node(x, l, r) = node(x', l', r') -> x = x', l = l', r = r'
            let constrENode = constructorEqRewrite(constrAppId, &constrENode, eg);

            // deduplicate constraint a = a1, l = l1, r = r1, t = node(a, l, r), t = node(a1, l1, l1) -> a = a1, l = l1, r = r1, t = node(a, l, r)
            // deduplicate enode calls a = a1, P(a, z), P(a1, z) -> a = a1, P(a, z)
            let updatedNewENode =
                dedupFromEqRewrite(constrAppId, &constrENode, newENodeAppId, newENode, eg);
        }

        println!("done constraintRewrite");
    });
    RewriteT {
        name: "constraintRewrite".to_owned(),
        searcher: searcher,
        applier: applier,
    }
    .into()
}

// TODO: only define from a list?
fn defineFromSharingBlock(
    unfoldList: &Rc<RefCell<UnfoldList>>,
    definedList: &Rc<RefCell<BTreeSet<CHC>>>,
    gCounter: &Rc<RefCell<u32>>,
) -> CHCRewrite {
    let pat = Pattern::parse("(new ?syntax ?cond <*1>)").unwrap();
    let patClone = pat.clone();
    let definedListClone = Rc::clone(definedList);
    let gCounterClone = Rc::clone(gCounter);
    let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<Subst> {
        ematch_all(eg, &patClone).into_iter().map(|s| s.0).collect()
    });
    let unfoldListClone = Rc::clone(unfoldList);
    let applier = Box::new(move |substs: Vec<Subst>, eg: &mut CHCEGraph| {
        for subst in substs {
            let rootAppId = pattern_subst(eg, &pat, &subst);

            let origENode = eg
                .getExactENodeInEGraph(&constructENodefromPatternSubst(eg, &pat, &subst).unwrap());
            let origENodeShape = origENode.weak_shape().0;
            let mut definedList = definedListClone.borrow_mut();
            if definedList.contains(&origENodeShape) {
                continue;
            }
            definedList.insert(origENodeShape);

            // TODO0: try change to rootData instead of mergeVarTypes
            let mut rootData = eg.analysis_data(rootAppId.id).varTypes.clone();
            let mut varToChildIndx: BTreeMap<Slot, Vec<usize>> = BTreeMap::default();
            let mut mergeVarTypes: BTreeMap<Slot, VarType> = BTreeMap::default();
            let childAppIds = &origENode.applied_id_occurrences()[2..];
            for indx in 0..childAppIds.len() {
                let appId = childAppIds[indx];
                for s in appId.slots() {
                    varToChildIndx.entry(s).or_insert(vec![]).push(indx);
                }

                let childrenVarTypes = &eg.analysis_data(appId.id).varTypes;
                mergeVarTypes.extend(
                    appId
                        .m
                        .clone()
                        .into_iter()
                        .map(|(from, to)| (to, *childrenVarTypes.get(&from).unwrap())),
                );
            }

            let mut unionfind: QuickUnionUf<UnionBySize> =
                QuickUnionUf::<UnionBySize>::new(childAppIds.len());
            let mut hasNonBasicVar = vec![false; childAppIds.len()];

            for (var, childrenIndx) in &varToChildIndx {
                if isNonBasicVar(&mergeVarTypes[var]) {
                    let leader = childrenIndx.first().unwrap();
                    for next in childrenIndx {
                        unionfind.union(*leader, *next);
                        hasNonBasicVar[*next] = true;
                    }
                }
            }

            // parition into groups, only get the one that contains non-basic var
            let mut groupMap = BTreeMap::<usize, Vec<usize>>::default();
            for i in 0..unionfind.size() {
                if hasNonBasicVar[i] {
                    let leader = unionfind.find(i);
                    groupMap.entry(leader).or_insert(vec![]).push(i);
                }
            }

            // for each group, define new chc
            for (_, group) in groupMap {
                let mut basicVars: BTreeSet<Slot> = BTreeSet::default();
                for i in &group {
                    let appId = childAppIds[*i];
                    for var in appId.slots() {
                        if !isNonBasicVar(&mergeVarTypes[&var]) {
                            basicVars.insert(var);
                        }
                    }
                }

                let mut children: Vec<_> =
                    group.clone().into_iter().map(|i| childAppIds[i]).collect();
                children.sort();
                // debug!("from {:?} children after sort {:?}", rootAppId.id, children);

                let dummyChildren = children
                    .clone()
                    .into_iter()
                    .map(|a| AppliedIdOrStar::AppliedId(a.clone()))
                    .collect();
                let emptyPredId = eg.add(CHC::PredSyntax(vec![]));
                let emptyAndId = eg.add(CHC::And(vec![]));
                let dummyEnode = CHC::New(emptyPredId, emptyAndId, dummyChildren);

                let (dummyEnodeSh, map) = dummyEnode.weak_shape();
                let mut basicVars: Vec<_> =
                    basicVars.into_iter().map(|s| map.inverse()[s]).collect();
                basicVars.sort();

                let basicVarsStr = basicVars
                    .into_iter()
                    .map(|s| generateVar(&s.to_string(), mergeVarTypes[&map[s]].clone()))
                    .collect::<Vec<_>>()
                    .join(" ");
                let syntax = format!("(pred <{basicVarsStr}>)");
                let syntaxId = eg.addExpr(&syntax);

                let oldLen = eg.total_number_of_nodes();

                let mut childrenStr = "".to_string();
                let mut newSubst = Subst::default();
                for i in 0..children.len() {
                    newSubst.insert(
                        format!("x{}", i),
                        children[i].clone().apply_slotmap(&map.inverse()),
                    );
                    childrenStr += &format!("?x{} ", i);
                }
                let newENodeStr = format!("(new {syntax} (and <>) <{childrenStr}>)");
                let newENodeAppId =
                    pattern_subst(eg, &Pattern::parse(&newENodeStr).unwrap(), &newSubst);
                let newENode = constructENodefromPatternSubst(
                    eg,
                    &Pattern::parse(&newENodeStr).unwrap(),
                    &newSubst,
                )
                .unwrap();

                if eg.total_number_of_nodes() == oldLen {
                    continue;
                }

                eg.shrink_slots(&newENodeAppId, &syntaxId.slots(), ());

                let newENodeShape = newENode.weak_shape().0;
                let composeEnode =
                    CHC::Compose(vec![AppliedIdOrStar::AppliedId(newENodeAppId.clone())]);
                let composeShape = composeEnode.weak_shape().0;
                let composeAppId = eg.add(composeEnode);
                checkVarType(&composeAppId, eg);

                addToUnfoldList(
                    &unfoldListClone,
                    UnfoldListComponent {
                        composeAppId: composeAppId,
                        composeShape: composeShape,
                        newEClassAppId: newENodeAppId,
                        newENodeShape: newENodeShape,
                    },
                );
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

// TODO: swapping unfold and define creates some error which should not be
pub fn getAllRewrites(
    unfoldList: &Rc<RefCell<UnfoldList>>,
    constrRewriteList: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    definedList: &Rc<RefCell<BTreeSet<CHC>>>,
    gCounter: &Rc<RefCell<u32>>,
    doConstraintRewrite: bool,
) -> Vec<CHCRewrite> {
    let mut rewrites = vec![unfold(unfoldList, constrRewriteList, gCounter)];

    if doConstraintRewrite {
        rewrites.push(constraintRewrite(constrRewriteList));
    }

    rewrites.extend([
        defineFromSharingBlock(unfoldList, definedList, gCounter),
        trueToAnd(),
    ]);

    rewrites
}
