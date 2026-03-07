use super::*;
use crate::*;

#[derive(Debug, Clone)]
// recipe for creating unfolded ENode
// contributes to one CHC rule
pub struct UnfoldResult {
    syntax1: AppliedId,
    mergeAndChildren: OrderVec<AppliedIdOrStar>,
    unfoldedChildren: OrderVec<AppliedIdOrStar>,
    new2AppId: AppliedId,
}

#[derive(Debug)]
pub struct ComposeUnfoldRecipe {
    // keeps multiple choices
    // e.g. we want to unfold p <- q
    // and q has 3 rules:
    // 1) q <- r1 equivalent to q <- r2,
    // 2) q <- s1 equivalent to q <- s2,
    // 3) q <- t1 equivalent to q <- t2
    // then we can unfold into
    // p <- ri, p <- sj, p <- tk using any combination of i, j, k in {1, 2}
    // Hence, Vec<Vec<UnfoldResult>> is
    // [[result from using q <- r1, result from using q <- r2],
    // [result from using q <- s1, result from using q <- s2],
    // [result from using q <- t1, result from using q <- t2]]
    unfoldResult: Vec<Vec<UnfoldResult>>,
    compose1ReplaceIdx: usize,
    compose1Children: OrderVec<AppliedId>,
    compose1AppId: AppliedId,
    compose2AppId: AppliedId,
    new1ReplaceIdx: usize,
    new1AppId: AppliedId,
    composeUnfoldRecipeTag: String,
}

pub struct UnfoldOption {
    pub composeUnfoldRecipe: ComposeUnfoldRecipe,
    pub createOrMerge: UnfoldOpType, //if true, will merge with information from composeRecipe, if false, will create
    pub extraTag: String,
}

#[derive(Debug, Clone, Ord, PartialEq, PartialOrd, Eq)]
pub struct UnfoldListElement {
    targetCompose1AppId: AppliedId,
    targetCompose1Shape: CHC,
    targetNew1AppId: AppliedId,
    targetNew1ENodeShape: CHC,
}

impl UnfoldListElement {
    pub fn find(&self, eg: &CHCEGraph) -> UnfoldListElement {
        UnfoldListElement {
            targetCompose1AppId: eg.find_applied_id(&self.targetCompose1AppId),
            targetCompose1Shape: eg.find_enode(&self.targetCompose1Shape),
            targetNew1AppId: eg.find_applied_id(&self.targetNew1AppId),
            targetNew1ENodeShape: eg.find_enode(&self.targetNew1ENodeShape),
        }
    }

    pub fn getShape(&self) -> (UnfoldListElement, SlotMap) {
        debug!("toBeUnfolded before getShape {self:#?}");
        let (targetCompose1Shape, m) = self.targetCompose1Shape.weak_shape();

        let ret = (
            UnfoldListElement {
                targetCompose1AppId: self.targetCompose1AppId.apply_slotmap(&m.inverse()),
                targetCompose1Shape,
                targetNew1AppId: self.targetNew1AppId.apply_slotmap(&m.inverse()),
                targetNew1ENodeShape: self.targetNew1ENodeShape.clone(),
            },
            m,
        );

        debug!("toBeUnfolded after getShape {:#?}", ret.0);

        ret
    }
}

pub type UnfoldList = DedupVec<(UnfoldListElement)>;

#[derive(PartialEq, Eq, Debug)]
pub enum UnfoldOpType {
    UnfoldMerge, //merge is for normal unfold, which will unfold and merge with the old compose
    UnfoldCreateOnly, //create is for unfold occur in define, which will only create unfolded nodes, there's no old compose.
}

fn addToUnfoldList(unfoldList: &Rc<RefCell<UnfoldList>>, toBeUnfolded: UnfoldListElement) {
    trace!("pushing to unfoldList {:?}", toBeUnfolded.getShape().0);

    let CHC::New(_, _, new1Children) = &toBeUnfolded.targetNew1ENodeShape else {
        panic!();
    };

    if new1Children.len() == 0 {
        debug!("skip toBeUnfolded {toBeUnfolded:#?}");
        return;
    }

    let mut unfoldListCopy = Rc::clone(unfoldList);
    unfoldListCopy.borrow_mut().push(toBeUnfolded);
}

// note: i1, compose1Children, composeAppId, new1EClass can be null if called from define
pub fn prepareUnfold(
    targetCompose1Shape: Option<&CHC>,
    compose1ReplaceIdx: usize,
    compose1Children: &OrderVec<AppliedId>,
    compose1AppId: &AppliedId,
    new1AppId: &AppliedId,
    new1ENode: &CHC,
    composeUnfoldRecipe: &mut Vec<ComposeUnfoldRecipe>,
    eg: &CHCEGraph,
) {
    trace!("unfoldSearch new1 {new1ENode:?}");
    let (syntax1, cond1, new1Children) = match new1ENode.clone() {
        CHC::New(syntax1, cond1, new1Children) => (syntax1, cond1, new1Children),
        _ => panic!(),
    };

    let and1Children = getAnyAndChildren(&cond1, eg);
    for (new1ReplaceIdx, compose2AppId) in new1Children.iter().enumerate() {
        let compose2AppId = compose2AppId.getAppliedId();
        let compose2ENodes = eg.enodes_applied(&compose2AppId);
        trace!("unfoldSearch compose2ENodes {compose2ENodes:?}");
        assert!(
            compose2ENodes.iter().any(|c| matches!(c, CHC::Compose(..))),
            "a class with ComposeInit does not have Compose, {}",
            compose2AppId
        );
        for compose2ENode in compose2ENodes {
            if let CHC::ComposeInit(..) = compose2ENode {
                continue;
            }

            let compose2ENode = eg.find_enode(&compose2ENode);
            trace!("unfoldSearch compose2ENode {compose2ENode:?}");
            let CHC::Compose(compose2Children) = compose2ENode else {
                panic!();
            };

            let mut unfoldedResults: Vec<Vec<UnfoldResult>> = vec![];
            for new2AppId in compose2Children.iter() {
                let new2AppId = new2AppId.getAppliedId();
                let mut unfoldedFromThisEClass: Vec<UnfoldResult> = vec![];
                let new2Vec = eg.enodes_applied(&new2AppId);
                assert!(new2Vec.len() > 0);
                for new2 in new2Vec {
                    checkNewENode!(new2, eg);
                    let CHC::New(syntax2, cond2, new2Children) = new2 else {
                        panic!();
                    };

                    let mut unfoldedChildren = OrderVec::new();
                    for i in 0..new1Children.len() {
                        if i == new1ReplaceIdx {
                            // replace this position with unfolded (new2) children
                            unfoldedChildren.extend(new2Children.clone());
                        } else {
                            unfoldedChildren.push(new1Children[i].clone());
                        }
                    }

                    // TODO: is this correct? Can it be any and children?
                    let and2Children = getAnyAndChildren(&cond2, eg);
                    let mut mergeAndChildren = OrderVec::new();
                    mergeAndChildren.extend(and1Children.clone());
                    mergeAndChildren.extend(and2Children);

                    checkNewENodeComponent!(
                        syntax1,
                        mergeAndChildren.clone(),
                        unfoldedChildren.clone()
                    );

                    // prepare for rewrite.
                    // cannot rewrite here because this is searcher only.
                    // separate search and rewrte.
                    unfoldedFromThisEClass.push(UnfoldResult {
                        syntax1: syntax1.clone(),
                        mergeAndChildren,
                        unfoldedChildren,
                        new2AppId: new2AppId.clone(),
                    });
                }
                //                 assert!(
                //                     unfoldedFromThisEClass.len() > 0,
                //                     "fromThisEClassRecipe is empty
                // eclass {}: {:?}",
                //                     new2AppId.id,
                //                     eg.eclass(new2AppId.id)
                //                 );
                assert!(
                    unfoldedFromThisEClass.len() > 0,
                    "fromThisEClassRecipe is empty
eclass {}: {:?}",
                    new2AppId.id,
                    eg.dumpEClassStr(new2AppId.id)
                );

                unfoldedResults.push(unfoldedFromThisEClass);
            }

            let x = ComposeUnfoldRecipe {
                unfoldResult: unfoldedResults,
                compose1ReplaceIdx,
                compose1Children: compose1Children.clone(),
                compose1AppId: compose1AppId.clone(),
                compose2AppId: compose2AppId.clone(),
                new1ReplaceIdx,
                new1AppId: new1AppId.clone(),
                composeUnfoldRecipeTag: format!(
                    "unfoldRule_{}_under_{:?}",
                    new1AppId.id, targetCompose1Shape
                ),
            };

            trace!("pushing to composeUnfoldRecipe {x:?}");

            composeUnfoldRecipe.push(x);
        }
    }

    assert!(composeUnfoldRecipe.len() > 0);
}

pub fn unfoldSearch(
    unfoldListCopy: &Rc<RefCell<UnfoldList>>,
    eg: &CHCEGraph,
) -> Vec<ComposeUnfoldRecipe> {
    let mut composeUnfoldRecipe = vec![];

    for toBeUnfolded in Rc::clone(&unfoldListCopy).borrow().iter() {
        let (
            UnfoldListElement {
                targetCompose1AppId,
                targetCompose1Shape,
                targetNew1AppId,
                targetNew1ENodeShape,
            },
            m,
        ) = toBeUnfolded.find(eg).getShape();

        let composeAppId = eg.find_applied_id(&targetCompose1AppId);
        let composeAppId = eg.mk_identity_applied_id(composeAppId.id);
        // TODO: change this to get
        let compose1ENode = eg.getExactENodeInEGraph(&targetCompose1Shape);
        trace!(
            "searching unfold on compose {:?}",
            compose1ENode.weak_shape().0
        );

        let CHC::Compose(compose1Children) = compose1ENode else {
            panic!();
        };

        let mut compose1Children: OrderVec<AppliedId> = compose1Children
            .into_iter()
            .map(AppliedIdOrStar::getAppliedIdOwn)
            .collect();
        let composeUnfoldRecipeLenBefore = composeUnfoldRecipe.len();

        if CHECKS {
            let mut compose1ChildrenIds: Vec<Id> = compose1Children
                .iter()
                .map(|x| eg.find_applied_id(x).id)
                .collect::<Vec<_>>();
            let oldLen = compose1ChildrenIds.len();
            compose1ChildrenIds.sort();
            compose1ChildrenIds.dedup();
            assert_eq!(compose1ChildrenIds.len(), oldLen);
        }

        // for (compose1ReplaceIdx, new1AppId) in compose1Children.iter().enumerate() {
        let compose1ReplaceIdx = compose1Children
            .iter()
            .position(|x| x.id == eg.find_applied_id(&targetNew1AppId).id)
            .unwrap();
        // if new1AppId.id != eg.find_applied_id(&targetNew1AppId).id {
        //     error!("skip new1AppId {:?}", new1AppId);
        //     continue;
        // }
        let new1AppId = &compose1Children[compose1ReplaceIdx];

        trace!("using new1AppId {:?}", new1AppId);

        let new1ENode = eg
            .getExactENodeInEClass(&targetNew1ENodeShape, &new1AppId.id)
            .apply_slotmap_partial(&new1AppId.m);

        checkNewENode!(new1ENode, eg);

        prepareUnfold(
            Some(&targetCompose1Shape),
            compose1ReplaceIdx,
            &compose1Children,
            &composeAppId,
            new1AppId,
            &new1ENode,
            &mut composeUnfoldRecipe,
            eg,
        );
        // }

        if composeUnfoldRecipe.len() == composeUnfoldRecipeLenBefore {
            panic!("skip this recipe");
        }
    }

    trace!("unfoldSearch return, composeUnfoldRecipe {composeUnfoldRecipe:?}");
    composeUnfoldRecipe
}

fn addUnfoldedNewENode(
    unfoldResultComb: Vec<UnfoldResult>,
    unfoldOption: &UnfoldOption,
    constrRewriteListCopy: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    eg: &mut CHCEGraph,
    createdNewENodes: &mut Vec<(AppliedId, CHC)>,
) {
    let UnfoldOption {
        composeUnfoldRecipe,
        createOrMerge,
        extraTag,
    } = unfoldOption;

    let ComposeUnfoldRecipe {
        unfoldResult,
        compose1ReplaceIdx,
        compose1Children,
        compose1AppId,
        compose2AppId,
        new1ReplaceIdx,
        new1AppId,
        composeUnfoldRecipeTag,
    } = composeUnfoldRecipe;

    trace!("addUnfoldedNewENode {composeUnfoldRecipe:?}");

    for UnfoldResult {
        syntax1,
        mut mergeAndChildren,
        mut unfoldedChildren,
        new2AppId,
    } in unfoldResultComb
    {
        let (unfoldedENode, mergeAnd, mergeAndAppId) =
            sortNewENode2(&syntax1, &mergeAndChildren, &unfoldedChildren, eg);

        checkVarType!(&mergeAndAppId, eg);

        match createOrMerge {
            UnfoldOpType::UnfoldCreateOnly => {
                eg.analysis_data_mut(mergeAndAppId.id)
                    .predNames
                    .insert(format!(
                        "and_from_unfold_define_{compose2AppId}_{new1ReplaceIdx}_using_{new2AppId}",
                    ));
            }
            UnfoldOpType::UnfoldMerge => {
                eg.analysis_data_mut(mergeAndAppId.id)
                    .predNames
                    .insert(format!(
                        "and_from_unfold_{compose2AppId}_{new1ReplaceIdx}_in_{}_using_{new2AppId}",
                        new1AppId.id
                    ));
            }
        }

        checkNewENode!(unfoldedENode, eg);

        let unfoldedENodeId = eg.add(unfoldedENode.clone());
        trace!(
            "call shrink slots with {unfoldedENodeId:?} {:?}",
            syntax1.slots()
        );
        eg.shrink_slots(&unfoldedENodeId, &syntax1.slots(), ());
        let unfoldedENodeId = eg.find_applied_id(&unfoldedENodeId);
        *eg.analysis_data_mut(unfoldedENodeId.id).varTypesMut() =
            getVarTypesAfterShrinked(&unfoldedENodeId, &syntax1.slots(), eg);

        let mut tag = if *createOrMerge == UnfoldOpType::UnfoldMerge {
            format!(
                "unfold_{compose2AppId}_{new1ReplaceIdx}_in_{}_using_{new2AppId}",
                new1AppId.id
            )
        } else {
            format!("define_unfold_{compose2AppId}_{new1ReplaceIdx}_using_{new2AppId}")
        };
        if extraTag != "" {
            tag = format!("{}_{}", tag, extraTag);
        }

        constrRewriteListCopy
            .borrow_mut()
            .push(ConstrRewriteComponent {
                constrAppId: mergeAndAppId.clone(),
                constrENode: mergeAnd,
                newENodeAppId: unfoldedENodeId.clone(),
                newENode: unfoldedENode.clone(),
                tag: tag.clone(),
            });

        checkVarType!(&unfoldedENodeId, eg);

        debug!("adding unfoldedENode {tag} {unfoldedENodeId:?} {unfoldedENode:?}");
        eg.analysis_data_mut(unfoldedENodeId.id)
            .predNames
            .insert(tag);

        trace!("createdNewENodes {unfoldedENodeId:?} {unfoldedENode:?}");
        createdNewENodes.push((unfoldedENodeId.clone(), unfoldedENode.clone()));
    }
}

fn createUnfoldedCompose(
    composeUnfoldRecipe: &ComposeUnfoldRecipe,
    createdNewENodes: &Vec<(AppliedId, CHC)>,
    createdComposeAppIds: &mut Vec<AppliedId>,
    createOrMerge: &UnfoldOpType,
    eg: &mut CHCEGraph,
) -> (AppliedId, CHC) {
    let ComposeUnfoldRecipe {
        unfoldResult,
        compose1ReplaceIdx,
        compose1Children,
        compose1AppId,
        compose2AppId,
        new1ReplaceIdx,
        new1AppId,
        composeUnfoldRecipeTag,
    } = composeUnfoldRecipe;

    let ret = match createOrMerge {
        // merge with the existsing before
        UnfoldOpType::UnfoldMerge => {
            let mut unfoldedComposeChildren = compose1Children.clone();
            unfoldedComposeChildren.remove(*compose1ReplaceIdx);
            unfoldedComposeChildren.extend(createdNewENodes.iter().map(|x| x.0.clone()));

            let unfoldedComposeChildren: OrderVec<_> = sortAppId(&unfoldedComposeChildren, true)
                .into_iter()
                .map(AppliedIdOrStar::from)
                .collect();
            let composeENode = CHC::Compose(unfoldedComposeChildren);

            let unfoldedComposeAppId = eg.add(composeENode.clone());
            debug!(
                "UnfoldOpType::UnfoldMerge added composeENode {:?}",
                composeENode.weak_shape().0
            );

            checkVarType!(&unfoldedComposeAppId, eg);
            eg.union_justified(
                &compose1AppId,
                &unfoldedComposeAppId,
                Some("unfold".to_owned()),
            );
            createdComposeAppIds.push(unfoldedComposeAppId.clone());

            (unfoldedComposeAppId, composeENode)
        }
        // just create unfold node
        UnfoldOpType::UnfoldCreateOnly => {
            // TODO: can change this funciton to iter, so we dont have to create a vec
            let composeChildren = sortAppId(
                &createdNewENodes.iter().map(|x| x.0.clone()).collect(),
                true,
            );
            let composeChildren: OrderVec<_> = composeChildren
                .into_iter()
                .map(AppliedIdOrStar::from)
                .collect();
            let composeENode = CHC::Compose(composeChildren);
            debug!(
                "UnfoldOpType::UnfoldMerge added composeENode {:?}",
                composeENode.weak_shape().0
            );

            let composeAppId = eg.add(composeENode.clone());
            createdComposeAppIds.push(composeAppId.clone());

            (composeAppId, composeENode)
        }
    };

    trace!("createUnfoldedCompose return {ret:?}");

    ret
}

pub fn unfoldApplyInternal(
    unfoldOption: &UnfoldOption,
    unfoldList: &Rc<RefCell<UnfoldList>>,
    constrRewriteList: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    eg: &mut CHCEGraph,
) -> Vec<AppliedId> {
    let UnfoldOption {
        composeUnfoldRecipe,
        createOrMerge,
        extraTag,
    } = unfoldOption;

    let ComposeUnfoldRecipe {
        unfoldResult,
        compose1ReplaceIdx,
        compose1Children,
        compose1AppId,
        compose2AppId,
        new1ReplaceIdx,
        new1AppId,
        composeUnfoldRecipeTag,
    } = composeUnfoldRecipe;

    trace!(
        "unfolding {compose2AppId} (index {new1ReplaceIdx}) in {} under {compose1AppId}",
        new1AppId.id
    );
    // trace!("root compose eclass {:?}", eg.eclass(compose1AppId.id));
    // trace!("new1EClass eclass {:?}", eg.eclass(new1AppId.id));
    // trace!("used eclass {:?}", eg.eclass(compose2AppId.id));
    trace!(
        "root compose eclass {:?}",
        eg.dumpEClassStr(compose1AppId.id)
    );
    trace!("new1EClass eclass {:?}", eg.dumpEClassStr(new1AppId.id));
    trace!("used eclass {:?}", eg.dumpEClassStr(compose2AppId.id));

    if *createOrMerge == UnfoldOpType::UnfoldCreateOnly {
        assert_eq!(compose1Children, &vec![].into());
        assert_eq!(compose1AppId, &AppliedId::null());
        assert_eq!(compose1ReplaceIdx, &0);
        assert_eq!(new1AppId, &AppliedId::null());
    }

    trace!("composeUnfoldRecipe {composeUnfoldRecipe:?}");

    let unfoldResultCombs = combination(&unfoldResult);
    assert!(
        unfoldResultCombs.len() > 0,
        "unfoldRecipeCombs is empty
unfoldResult {unfoldResult:#?}"
    );

    let mut createdComposeAppIds = vec![];
    for unfoldResultComb in unfoldResultCombs {
        let mut createdNewENodes = vec![];
        addUnfoldedNewENode(
            unfoldResultComb,
            unfoldOption,
            constrRewriteList,
            eg,
            &mut createdNewENodes,
        );

        trace!("createdNewENodes {createdNewENodes:?}");

        let (composeAppId, composeShape) = createUnfoldedCompose(
            composeUnfoldRecipe,
            &createdNewENodes,
            &mut createdComposeAppIds,
            createOrMerge,
            eg,
        );

        // TODO: we only continue to unfold on newly created ones, is this correct?
        // for (i, (enodeId, enode)) in createdNewENodes.into_iter().enumerate() {
        //     addToUnfoldList(
        //         &unfoldList,
        //         UnfoldListElement {
        //             targetCompose1AppId: composeAppId.clone(),
        //             targetCompose1Shape: composeShape.clone(),
        //             targetNew1AppId: enodeId,
        //             targetNew1ENodeShape: enode,
        //         },
        //     );
        // }

        let CHC::Compose(composeChildren) = &composeShape else {
            panic!();
        };

        trace!(
            "adding to unfoldList from {:?}",
            composeShape.weak_shape().0
        );
        for new1AppId in composeChildren.iter() {
            let new1AppId = eg.find_applied_id(&new1AppId.getAppliedId());
            let new1ENodes = eg.enodes_applied(&new1AppId);
            for new1ENode in new1ENodes {
                addToUnfoldList(
                    &unfoldList,
                    UnfoldListElement {
                        targetCompose1AppId: composeAppId.clone(),
                        targetCompose1Shape: composeShape.clone(),
                        targetNew1AppId: new1AppId.clone(),
                        targetNew1ENodeShape: new1ENode,
                    },
                );
            }
        }
    }

    assert!(createdComposeAppIds.len() > 0);
    createdComposeAppIds
}

pub fn unfoldApply(
    unfoldList: &Rc<RefCell<UnfoldList>>,
    composeUnfoldRecipes: Vec<ComposeUnfoldRecipe>,
    constrRewriteListCopy: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    eg: &mut CHCEGraph,
) {
    Rc::clone(&unfoldList).borrow_mut().clear();
    for composeUnfoldRecipe in composeUnfoldRecipes.into_iter() {
        unfoldApplyInternal(
            &UnfoldOption {
                composeUnfoldRecipe,
                createOrMerge: UnfoldOpType::UnfoldMerge,
                extraTag: "".to_string(),
            },
            unfoldList,
            constrRewriteListCopy,
            eg,
        );
    }
}

// H <- A, B, C unfolding using A one time, B one time, C one time
// H <- A', B, C
// H <- A, B', C
// H <- A, B, C'
pub fn unfold(
    unfoldList: &Rc<RefCell<UnfoldList>>,
    constrRewriteList: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
) -> CHCRewrite {
    let unfoldListCopy = Rc::clone(unfoldList);

    let constrRewriteListCopy = Rc::clone(constrRewriteList);

    // unfoldList is taken by searcher
    let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<ComposeUnfoldRecipe> {
        unfoldSearch(&unfoldListCopy, eg)
    });

    let unfoldListCopy2 = Rc::clone(unfoldList);
    // unfoldList is cleared before applier, to add new element to it
    let applier = Box::new(
        move |composeRecipes: Vec<ComposeUnfoldRecipe>, eg: &mut CHCEGraph| {
            unfoldApply(&unfoldListCopy2, composeRecipes, &constrRewriteListCopy, eg);
        },
    );

    RewriteT {
        name: "unfold".to_owned(),
        searcher: searcher,
        applier: applier,
    }
    .into()
}
