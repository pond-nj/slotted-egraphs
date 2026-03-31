#[cfg(not(feature = "parallelAdd"))]
use std::cell::RefMut;
#[cfg(feature = "parallelAdd")]
use std::sync::{RwLockReadGuard, RwLockWriteGuard};

use super::*;
use crate::*;
use rayon::prelude::*;

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

#[cfg(not(feature = "parallelAdd"))]
#[derive(Default, Clone)]
pub struct ConstrCheckedCache {
    pub unsatCache: Rc<RefCell<BTreeSet<CHC>>>,
    pub satCache: Rc<RefCell<BTreeSet<CHC>>>,
    pub hits: Rc<RefCell<usize>>,
    pub misses: Rc<RefCell<usize>>,
}

#[cfg(feature = "parallelAdd")]
#[derive(Default, Clone)]
pub struct ConstrCheckedCache {
    pub unsatCache: Arc<RwLock<BTreeSet<CHC>>>,
    pub satCache: Arc<RwLock<BTreeSet<CHC>>>,
    pub hits: Arc<RwLock<usize>>,
    pub misses: Arc<RwLock<usize>>,
}

impl ConstrCheckedCache {
    #[cfg(feature = "parallelAdd")]
    pub fn getUnsatCache(&self) -> RwLockReadGuard<BTreeSet<CHC>> {
        self.unsatCache.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getUnsatCache(&self) -> Ref<BTreeSet<CHC>> {
        self.unsatCache.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getUnsatCacheMut(&self) -> RwLockWriteGuard<BTreeSet<CHC>> {
        self.unsatCache.write().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getUnsatCacheMut(&self) -> RefMut<'_, BTreeSet<CHC>> {
        self.unsatCache.borrow_mut()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getSatCache(&self) -> RwLockReadGuard<BTreeSet<CHC>> {
        self.satCache.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getSatCache(&self) -> Ref<BTreeSet<CHC>> {
        self.satCache.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getSatCacheMut(&self) -> RwLockWriteGuard<BTreeSet<CHC>> {
        self.satCache.write().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getSatCacheMut(&self) -> RefMut<'_, BTreeSet<CHC>> {
        self.satCache.borrow_mut()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getHits(&self) -> RwLockReadGuard<usize> {
        self.hits.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getHits(&self) -> Ref<usize> {
        self.hits.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getHitsMut(&self) -> RwLockWriteGuard<usize> {
        self.hits.write().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getHitsMut(&self) -> RefMut<'_, usize> {
        self.hits.borrow_mut()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getMisses(&self) -> RwLockReadGuard<usize> {
        self.misses.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getMisses(&self) -> Ref<usize> {
        self.misses.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getMissesMut(&self) -> RwLockWriteGuard<usize> {
        self.misses.write().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getMissesMut(&self) -> RefMut<'_, usize> {
        self.misses.borrow_mut()
    }
}

#[derive(Default, Clone)]
pub struct UnfoldHelper {
    #[cfg(not(feature = "parallelAdd"))]
    pub unfoldList: Rc<RefCell<UnfoldList>>,
    #[cfg(feature = "parallelAdd")]
    pub unfoldList: Arc<RwLock<UnfoldList>>,
    // set of CHC::AND that are false according to z3
    pub constrCheckedCache: ConstrCheckedCache,
}

impl UnfoldHelper {
    #[cfg(feature = "parallelAdd")]
    pub fn getUnfoldList(&self) -> RwLockReadGuard<UnfoldList> {
        self.unfoldList.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getUnfoldList(&self) -> Ref<UnfoldList> {
        self.unfoldList.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getUnfoldListMut(&self) -> RwLockWriteGuard<UnfoldList> {
        self.unfoldList.write().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getUnfoldListMut(&self) -> RefMut<'_, UnfoldList> {
        self.unfoldList.borrow_mut()
    }
}

#[derive(PartialEq, Eq, Debug)]
pub enum UnfoldOpType {
    UnfoldMerge, //merge is for normal unfold, which will unfold and merge with the old compose
    UnfoldCreateOnly, //create is for unfold occur in define, which will only create unfolded nodes, there's no old compose.
}

fn addToUnfoldList(unfoldHelper: &UnfoldHelper, toBeUnfolded: UnfoldListElement) {
    trace!("pushing to unfoldList {:?}", toBeUnfolded.getShape().0);

    let CHC::New(_, _, new1Children) = &toBeUnfolded.targetNew1ENodeShape else {
        panic!();
    };

    if new1Children.len() == 0 {
        debug!("skip toBeUnfolded {toBeUnfolded:#?}");
        return;
    }

    unfoldHelper.getUnfoldListMut().push(toBeUnfolded);
}

fn isUnsatConstr(
    andChildren: &OrderVec<AppliedId>,
    constrCheckedCache: &ConstrCheckedCache,
    eg: &CHCEGraph,
) -> bool {
    let sortedMergeAndChildren = sortAppId(&andChildren, true, eg.canonAppIdsCache());

    let mut andCHC = CHC::And(
        sortedMergeAndChildren
            .into_iter()
            .map(AppliedIdOrStar::from)
            .collect(),
    );
    andCHC.weak_shapeMut();

    if constrCheckedCache.getUnsatCache().contains(&andCHC) {
        *constrCheckedCache.getHitsMut() += 1;
        return true;
    }
    if constrCheckedCache.getSatCache().contains(&andCHC) {
        *constrCheckedCache.getHitsMut() += 1;
        return false;
    }

    *constrCheckedCache.getMissesMut() += 1;

    let result = solveZ3Constraint(&andCHC, eg);
    if result == SatStatus::Unsat {
        constrCheckedCache.getUnsatCacheMut().insert(andCHC);
        return true;
    }
    assert_eq!(result, SatStatus::Sat);
    constrCheckedCache.getSatCacheMut().insert(andCHC);

    return false;
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
    constrCheckedCache: &ConstrCheckedCache,
    eg: &CHCEGraph,
) {
    let (syntax1, cond1, new1Children) = match new1ENode.clone() {
        CHC::New(syntax1, cond1, new1Children) => (syntax1, cond1, new1Children),
        _ => panic!(),
    };

    // let eg = getEgNoMut(eg);
    let and1Children = getAnyAndChildren(&cond1, &eg);
    for (new1ReplaceIdx, compose2AppId) in new1Children.iter().enumerate() {
        let compose2AppId = compose2AppId.getAppliedId();
        let compose2AppId = eg.find_applied_id(&compose2AppId);
        let compose2ENodes = eg.enodes_applied(&compose2AppId);
        if CHECKS {
            assert!(
                compose2ENodes.iter().any(|c| matches!(c, CHC::Compose(..))),
                "a class with ComposeInit does not have Compose, {}",
                compose2AppId
            );
        }
        for compose2ENode in compose2ENodes {
            if let CHC::ComposeInit(..) = compose2ENode {
                continue;
            }

            let compose2ENode = eg.find_enode(&compose2ENode);
            let CHC::Compose(compose2Children) = compose2ENode else {
                panic!();
            };

            let mut unfoldedResults: Vec<Vec<UnfoldResult>> = vec![];
            'new2AppIdLoop: for new2AppId in compose2Children.iter() {
                let new2AppId = new2AppId.getAppliedId();
                let mut unfoldedFromThisEClass: Vec<UnfoldResult> = vec![];
                let new2Vec = eg.enodes_applied(&new2AppId);
                assert!(new2Vec.len() > 0);
                for new2 in new2Vec {
                    checkNewENode!(new2, &eg);
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
                    let and2Children = getAnyAndChildren(&cond2, &eg);
                    let mut mergeAndChildren = OrderVec::new();
                    mergeAndChildren.extend(and1Children.clone());
                    mergeAndChildren.extend(and2Children);

                    if CHECK_UNSAT_CONSTR {
                        let isUnsat = isUnsatConstr(
                            &mergeAndChildren
                                .iter()
                                .map(AppliedIdOrStar::getAppliedId)
                                .collect(),
                            &constrCheckedCache,
                            &eg,
                        );
                        if isUnsat {
                            continue;
                        }
                    }

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
                if CHECK_UNSAT_CONSTR && unfoldedFromThisEClass.len() == 0 {
                    continue 'new2AppIdLoop;
                }

                if CHECKS {
                    assert!(
                        unfoldedFromThisEClass.len() > 0,
                        "unfoldedFromThisEClass is empty
eclass {}: {:?}",
                        new2AppId.id,
                        eg.dumpEClassStr(new2AppId.id)
                    );
                }

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

            composeUnfoldRecipe.push(x);
        }
    }

    if composeUnfoldRecipe.len() == 0 {
        error!("eg {:?}", eg);
        error!("compose1ReplaceIdx {}", compose1ReplaceIdx);
        error!("compose1Children {:?}", compose1Children);
        error!("compose1AppId {:?}", compose1AppId);
        error!("new1AppId {:?}", new1AppId);
        error!("new1ENode {:?}", new1ENode);
    }
    assert!(composeUnfoldRecipe.len() > 0);
}

pub fn unfoldSearchAndPrepare(
    unfoldHelper: &UnfoldHelper,
    eg: &CHCEGraph,
) -> Vec<ComposeUnfoldRecipe> {
    info!("start unfoldSearchAndPrepare");
    let UnfoldHelper {
        unfoldList,
        constrCheckedCache,
    } = unfoldHelper;
    let unfoldList = unfoldHelper.getUnfoldList();
    let mut composeUnfoldRecipe = vec![];

    for toBeUnfolded in unfoldList.iter() {
        if CHECKS {
            let mut targetNew1ENodeShape = toBeUnfolded.targetNew1ENodeShape.clone();
            targetNew1ENodeShape.weak_shapeMut();
            assert!(
                eg.getENodeId(&targetNew1ENodeShape).is_some(),
                "{:?}
{:?}",
                toBeUnfolded.targetNew1ENodeShape,
                targetNew1ENodeShape
            );
        }

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

        let compose1ReplaceIdx = compose1Children
            .iter()
            .position(|x| x.id == eg.find_applied_id(&targetNew1AppId).id)
            .unwrap();
        let new1AppId = &compose1Children[compose1ReplaceIdx];

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
            constrCheckedCache,
            &eg,
        );

        if composeUnfoldRecipe.len() == composeUnfoldRecipeLenBefore {
            panic!("skip this recipe");
        }
    }

    trace!("unfoldSearch return, composeUnfoldRecipe {composeUnfoldRecipe:?}");
    info!("end unfoldSearchAndPrepare");
    composeUnfoldRecipe
}

#[cfg(not(feature = "parallelAdd"))]
pub fn getEg(eg: &mut CHCEGraph) -> &mut CHCEGraph {
    eg
}

#[cfg(feature = "parallelAdd")]
pub fn getEg<'a>(eg: &'a RwLock<&'a mut CHCEGraph>) -> RwLockReadGuard<'a, &'a mut CHCEGraph> {
    eg.read().unwrap()
}

#[cfg(feature = "parallelAdd")]
pub fn getEgNoMut<'a>(eg: &'a RwLock<&'a CHCEGraph>) -> RwLockReadGuard<'a, &'a CHCEGraph> {
    eg.read().unwrap()
}

#[cfg(not(feature = "parallelAdd"))]
pub fn getEgMut(eg: &mut CHCEGraph) -> &mut CHCEGraph {
    eg
}

#[cfg(feature = "parallelAdd")]
pub fn getEgMut<'a>(eg: &'a RwLock<&'a mut CHCEGraph>) -> RwLockWriteGuard<'a, &'a mut CHCEGraph> {
    eg.write().unwrap()
}

fn addUnfoldedNewENode<'a>(
    unfoldResultComb: Vec<UnfoldResult>,
    unfoldOption: &UnfoldOption,
    constrRewriteListCopy: &ConstrRewriteList,
    #[cfg(not(feature = "parallelAdd"))] eg: &mut CHCEGraph,
    #[cfg(feature = "parallelAdd")] eg: &'a RwLock<&'a mut CHCEGraph>,
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

        {
            let egRead = getEg(eg);
            checkVarType!(&mergeAndAppId, &egRead);
        }

        let mut egMut = getEgMut(eg);
        match createOrMerge {
            UnfoldOpType::UnfoldCreateOnly => {
                egMut.updateAnalysisData(mergeAndAppId.id, |data| {
                    data.predNames.insert(format!(
                        "and_from_unfold_define_{compose2AppId}_{new1ReplaceIdx}_using_{new2AppId}",
                    ));
                });
            }
            UnfoldOpType::UnfoldMerge => {
                egMut.updateAnalysisData(mergeAndAppId.id, |data| {
                    data.predNames.insert(format!(
                        "and_from_unfold_{compose2AppId}_{new1ReplaceIdx}_in_{}_using_{new2AppId}",
                        new1AppId.id
                    ));
                });
            }
        }

        checkNewENode!(unfoldedENode, &egMut);
        {
            let mut unfoldedENode = unfoldedENode.clone();
            unfoldedENode.weak_shapeMut();
            debug!(
                "{:?} unfoldedENode {unfoldedENode:?}",
                rayon::current_thread_index()
            );
        }
        let unfoldedENodeId = egMut.add(&unfoldedENode);
        trace!(
            "call shrink slots with {unfoldedENodeId:?} {:?}",
            syntax1.slots()
        );
        egMut.shrink_slots(&unfoldedENodeId, &syntax1.slots(), ());
        let unfoldedENodeId = egMut.find_applied_id(&unfoldedENodeId);
        let varTypeAfterShrink =
            getVarTypesAfterShrinked(&unfoldedENodeId, &syntax1.slots(), &egMut);
        egMut.updateAnalysisData(unfoldedENodeId.id, |data| {
            *data.varTypesMut() = varTypeAfterShrink;
        });

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

        #[cfg(not(feature = "parallelAdd"))]
        constrRewriteListCopy
            .borrow_mut()
            .push(ConstrRewriteComponent {
                constrAppId: mergeAndAppId.clone(),
                constrENode: mergeAnd,
                newENodeAppId: unfoldedENodeId.clone(),
                newENode: unfoldedENode.clone(),
                tag: tag.clone(),
            });

        #[cfg(feature = "parallelAdd")]
        constrRewriteListCopy
            .write()
            .unwrap()
            .push(ConstrRewriteComponent {
                constrAppId: mergeAndAppId.clone(),
                constrENode: mergeAnd,
                newENodeAppId: unfoldedENodeId.clone(),
                newENode: unfoldedENode.clone(),
                tag: tag.clone(),
            });

        checkVarType!(&unfoldedENodeId, &egMut);

        debug!("adding unfoldedENode {tag} {unfoldedENodeId:?} {unfoldedENode:?}");
        egMut.updateAnalysisData(unfoldedENodeId.id, |data| {
            data.predNames.insert(tag);
        });

        trace!("createdNewENodes {unfoldedENodeId:?} {unfoldedENode:?}");
        // if CHECKS {
        //     let mut unfoldedENode = unfoldedENode.clone();
        //     unfoldedENode.weak_shapeMut();
        //     assert!(egMut.getENodeId(&unfoldedENode).is_some());
        // }
        createdNewENodes.push((unfoldedENodeId.clone(), unfoldedENode.clone()));
    }
}

fn createUnfoldedCompose<'a>(
    composeUnfoldRecipe: &ComposeUnfoldRecipe,
    createdNewENodes: &Vec<(AppliedId, CHC)>,
    #[cfg(not(feature = "parallelAdd"))] createdComposeAppIds: &mut Vec<AppliedId>,
    #[cfg(feature = "parallelAdd")] createdComposeAppIds: &RwLock<Vec<AppliedId>>,
    createOrMerge: &UnfoldOpType,
    #[cfg(not(feature = "parallelAdd"))] eg: &mut CHCEGraph,
    #[cfg(feature = "parallelAdd")] eg: &'a RwLock<&'a mut CHCEGraph>,
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

            let unfoldedComposeChildren: OrderVec<_> = {
                sortAppId(&unfoldedComposeChildren, true, getEg(eg).canonAppIdsCache())
                    .into_iter()
                    .map(AppliedIdOrStar::from)
                    .collect()
            };
            let composeENode = CHC::Compose(unfoldedComposeChildren);
            let unfoldedComposeAppId = {
                let mut egMut = getEgMut(eg);
                // TODO: change to addShape
                let unfoldedComposeAppId = egMut.add(&composeENode);
                debug!(
                    "UnfoldOpType::UnfoldMerge added composeENode {:?}",
                    composeENode.weak_shape().0
                );

                checkVarType!(&unfoldedComposeAppId, egMut);
                egMut.union_justified(
                    &compose1AppId,
                    &unfoldedComposeAppId,
                    Some("unfold".to_owned()),
                );
                unfoldedComposeAppId
            };
            #[cfg(not(feature = "parallelAdd"))]
            createdComposeAppIds.push(unfoldedComposeAppId.clone());
            #[cfg(feature = "parallelAdd")]
            {
                let mut createdComposeAppIds = createdComposeAppIds.write().unwrap();
                createdComposeAppIds.push(unfoldedComposeAppId.clone());
            }

            (unfoldedComposeAppId, composeENode)
        }
        // just create unfold node
        UnfoldOpType::UnfoldCreateOnly => {
            // TODO: can change this funciton to iter, so we dont have to create a vec
            let composeChildren = {
                sortAppId(
                    &createdNewENodes.iter().map(|x| x.0.clone()).collect(),
                    true,
                    getEg(eg).canonAppIdsCache(),
                )
            };
            let composeChildren: OrderVec<_> = composeChildren
                .into_iter()
                .map(AppliedIdOrStar::from)
                .collect();
            let composeENode = CHC::Compose(composeChildren);
            debug!(
                "UnfoldOpType::UnfoldMerge added composeENode {:?}",
                composeENode.weak_shape().0
            );

            let composeAppId = {
                let mut egMut = getEgMut(eg);
                // TODO: change to addShape
                egMut.add(&composeENode)
            };

            #[cfg(not(feature = "parallelAdd"))]
            createdComposeAppIds.push(composeAppId.clone());
            #[cfg(feature = "parallelAdd")]
            {
                let mut createdComposeAppIds = createdComposeAppIds.write().unwrap();
                createdComposeAppIds.push(composeAppId.clone());
            }

            (composeAppId, composeENode)
        }
    };

    trace!("createUnfoldedCompose return {ret:?}");

    ret
}

pub fn unfoldApplyInternal<'a>(
    unfoldOption: &UnfoldOption,
    unfoldHelper: &UnfoldHelper,
    constrRewriteList: &ConstrRewriteList,
    #[cfg(not(feature = "parallelAdd"))] eg: &mut CHCEGraph,
    #[cfg(feature = "parallelAdd")] eg: &'a RwLock<&'a mut CHCEGraph>,
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

    {
        let egRead = getEg(eg);
        trace!(
            "unfolding {compose2AppId} (index {new1ReplaceIdx}) in {} under {compose1AppId}",
            new1AppId.id
        );
        trace!(
            "root compose eclass {:?}",
            egRead.dumpEClassStr(compose1AppId.id)
        );
        trace!("new1EClass eclass {:?}", egRead.dumpEClassStr(new1AppId.id));
        trace!("used eclass {:?}", egRead.dumpEClassStr(compose2AppId.id));
    }

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

    #[cfg(not(feature = "parallelAdd"))]
    let mut createdComposeAppIds = vec![];
    #[cfg(feature = "parallelAdd")]
    let mut createdComposeAppIds = RwLock::new(vec![]);

    unfoldResultCombs.into_iter().for_each(|unfoldResultComb| {
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
            #[cfg(not(feature = "parallelAdd"))]
            &mut createdComposeAppIds,
            #[cfg(feature = "parallelAdd")]
            &createdComposeAppIds,
            createOrMerge,
            eg,
        );

        let CHC::Compose(composeChildren) = &composeShape else {
            panic!();
        };

        trace!(
            "adding to unfoldList from {:?}",
            composeShape.weak_shape().0
        );
        let egRead = getEg(eg);
        for new1AppId in composeChildren.iter() {
            let new1AppId = egRead.find_applied_id(&new1AppId.getAppliedId());

            if CHECK_UNSAT_CONSTR
                && egRead.analysis_data(new1AppId.id).satStatus == SatStatus::Unsat
            {
                panic!();
                continue;
            }

            let new1ENodes = egRead.enodes_applied(&new1AppId);
            for new1ENode in new1ENodes {
                if CHECKS {
                    let mut new1ENode = new1ENode.clone();
                    new1ENode.weak_shapeMut();
                    assert!(egRead.getENodeId(&new1ENode).is_some(), "{:?}", new1ENode);
                }
                addToUnfoldList(
                    unfoldHelper,
                    UnfoldListElement {
                        targetCompose1AppId: composeAppId.clone(),
                        targetCompose1Shape: composeShape.clone(),
                        targetNew1AppId: new1AppId.clone(),
                        targetNew1ENodeShape: new1ENode,
                    },
                );
            }
        }
    });

    #[cfg(not(feature = "parallelAdd"))]
    assert!(createdComposeAppIds.len() > 0);
    #[cfg(feature = "parallelAdd")]
    assert!(createdComposeAppIds.read().unwrap().len() > 0);

    #[cfg(not(feature = "parallelAdd"))]
    return createdComposeAppIds;

    #[cfg(feature = "parallelAdd")]
    createdComposeAppIds.into_inner().unwrap()
}

pub fn unfoldApply<'a>(
    unfoldHelper: &UnfoldHelper,
    composeUnfoldRecipes: Vec<ComposeUnfoldRecipe>,
    constrRewriteListCopy: &ConstrRewriteList,
    #[cfg(not(feature = "parallelAdd"))] eg: &mut CHCEGraph,
    #[cfg(feature = "parallelAdd")] eg: &'a RwLock<&'a mut CHCEGraph>,
) {
    {
        unfoldHelper.getUnfoldListMut().clear();
    }
    for composeUnfoldRecipe in composeUnfoldRecipes.into_iter() {
        unfoldApplyInternal(
            &UnfoldOption {
                composeUnfoldRecipe,
                createOrMerge: UnfoldOpType::UnfoldMerge,
                extraTag: "".to_string(),
            },
            unfoldHelper,
            constrRewriteListCopy,
            eg,
        );
    }
}

pub fn unfoldHelperRebuild(unfoldHelper: &UnfoldHelper, eg: &CHCEGraph) {
    // TODO
    if CHECK_UNSAT_CONSTR {
        // todo!()
    }
}

// H <- A, B, C unfolding using A one time, B one time, C one time
// H <- A', B, C
// H <- A, B', C
// H <- A, B, C'
pub fn unfold(unfoldHelper: &UnfoldHelper, constrRewriteList: &ConstrRewriteList) -> CHCRewrite {
    let constrRewriteListCopy = constrRewriteList.clone();

    // unfoldList is taken by searcher
    let unfoldHelperClone = (*unfoldHelper).clone();
    let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<ComposeUnfoldRecipe> {
        unfoldHelperRebuild(&unfoldHelperClone, eg);
        unfoldSearchAndPrepare(&unfoldHelperClone, eg)
    });

    // unfoldList is cleared before applier, to add new element to it
    let unfoldHelperClone = (*unfoldHelper).clone();
    let applier = Box::new(
        move |composeRecipes: Vec<ComposeUnfoldRecipe>, eg: &mut CHCEGraph| {
            unfoldApply(
                &unfoldHelperClone,
                composeRecipes,
                &constrRewriteListCopy,
                #[cfg(not(feature = "parallelAdd"))]
                eg,
                #[cfg(feature = "parallelAdd")]
                &RwLock::new(eg),
            );
        },
    );

    RewriteT {
        name: "unfold".to_owned(),
        searcher: searcher,
        applier: applier,
    }
    .into()
}
