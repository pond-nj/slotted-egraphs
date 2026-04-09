use super::*;
use crate::*;

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
    trace!("doing expandEqRewrite");
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
                let eqChildAppId = eg.add(&eqChild);
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

    let (_, newConstraint, newConstraintAppId) = sortNewENode2(
        &syntax,
        &newConstraintChildren,
        &newENodeChildren,
        #[cfg(not(feature = "parallelAdd"))]
        eg,
        #[cfg(feature = "parallelAdd")]
        &RwLock::new(eg),
    );

    checkVarType!(&newConstraintAppId, eg);
    eg.updateAnalysisData(newConstraintAppId.id, |data| {
        data.predNames.insert(format!(
            "expandEqRewrite_{}_{}",
            constrAppId.id, originalNewENodeAppId.id
        ));
    });

    eg.union_justified(
        constrAppId,
        &newConstraintAppId,
        Some("expandEq".to_owned()),
    );

    trace!("done expandEqRewrite");
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
    trace!("doing constructorEqRewrite");
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
                        let newEqAppId = eg.add(&CHC::Eq(val.clone(), val2));
                        checkVarType!(&newEqAppId, eg);
                        andChildren.insert(AppliedIdOrStar::AppliedId(newEqAppId));
                    }

                    if l != l2 {
                        let newEqAppId = eg.add(&CHC::Eq(l.clone(), l2));
                        checkVarType!(&newEqAppId, eg);
                        andChildren.insert(AppliedIdOrStar::AppliedId(newEqAppId));
                    }

                    if r != r2 {
                        let newEqAppId = eg.add(&CHC::Eq(r.clone(), r2));
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
        #[cfg(not(feature = "parallelAdd"))]
        eg,
        #[cfg(feature = "parallelAdd")]
        &RwLock::new(eg),
    );

    eg.updateAnalysisData(newConstraintAppId.id, |data| {
        data.predNames.insert(format!(
            "constructorEqRewrite_fromConstr_{}_fromNewENode_{}",
            constrAppId.id, originalNewENodeAppId.id
        ));
    });

    checkVarType!(&newConstraintAppId, eg);
    eg.union_justified(
        &constrAppId,
        &newConstraintAppId,
        Some("constructorEqRewrite".to_owned()),
    );

    trace!("done constructorEqRewrite");
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

        let lookupRes = eg.lookupMut(&updatedChildENode);
        if lookupRes.is_some() {
            updatedChild = lookupRes;
            break;
        }

        let newUpdatedChild = eg.add(&updatedChildENode);
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
            let trueId = eg.add(&CHC::True());
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
    trace!("doing dedupFromEqRewrite");
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

    let (updatedNew, newConstraint, newConstraintAppId) = sortNewENode2(
        syntax,
        &updatedConstrChildren,
        &updatedNewChildren,
        #[cfg(not(feature = "parallelAdd"))]
        eg,
        #[cfg(feature = "parallelAdd")]
        &RwLock::new(eg),
    );
    eg.updateAnalysisData(newConstraintAppId.id, |data| {
        data.predNames.insert(format!(
            "dedupFromEqRewrite_fromConstr_{}_fromNewENode_{}",
            constrAppId.id, newENodeAppId.id
        ));
    });

    let updatedNewAppId = eg.add(&updatedNew.clone());

    eg.union_justified(
        &newENodeAppId,
        &updatedNewAppId,
        Some("dedupFromEqRewrite".to_owned()),
    );

    trace!("done dedupFromEqRewrite");
    (newConstraint, updatedNew)
}

pub fn constraintRewrite(rewriteList: &RewriteList) -> CHCRewrite {
    let searcher = Box::new(move |eg: &CHCEGraph| -> () {});
    let rewriteListClone = rewriteList.clone();
    let applier = Box::new(move |_: (), eg: &mut CHCEGraph| {
        for constrRewriteComponent in rewriteListClone.getConstrRewriteList().iter() {
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
            rewriteListClone
                .getFunctionalityComponentsListMut()
                .push(ConstrRewriteComponent {
                    constrAppId: constrAppId.clone(),
                    constrENode: newConstraint.clone(),
                    newENodeAppId: newENodeAppId.clone(),
                    newENode: updatedNewENode.clone(),
                    tag: "functionalityTransformation".to_owned(),
                });
        }

        rewriteListClone.getConstrRewriteListMut().clear();
    });
    RewriteT {
        name: "constraintRewrite".to_owned(),
        searcher: searcher,
        applier: applier,
    }
    .into()
}
