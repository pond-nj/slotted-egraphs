use super::*;
use crate::*;
use derive_more::derive;
use log::{debug, error, info, trace, warn};
#[cfg(not(feature = "parallelAdd"))]
use std::cell::RefMut;
use std::cell::{Ref, RefCell};

use std::f32::consts::E;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

use std::sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::time::{Duration, Instant};
use union_find::{QuickUnionUf, UnionBySize, UnionFind};
use vec_collections::VecSet;

static G_COUNTER: AtomicUsize = AtomicUsize::new(0);

use std::collections::HashSet;

mod unfold;
pub use unfold::*;

mod constraint;
pub use constraint::*;

mod defineFold;
pub use defineFold::*;

#[cfg(not(feature = "parallelAdd"))]
pub type ConstrRewriteList = Rc<RefCell<Vec<ConstrRewriteComponent>>>;
#[cfg(feature = "parallelAdd")]
pub type ConstrRewriteList = Arc<RwLock<Vec<ConstrRewriteComponent>>>;

pub struct RewriteStats {
    pub duplicateUnfold: usize,
}

#[derive(Default, Clone)]
pub struct RewriteList {
    unfoldHelper: UnfoldHelper,
    constrRewriteList: ConstrRewriteList,
    functionalityComponentsList: ConstrRewriteList,
    defineHelper: DefineHelper,
}

impl RewriteList {
    #[cfg(not(feature = "parallelAdd"))]
    pub fn getConstrRewriteList(&self) -> Ref<Vec<ConstrRewriteComponent>> {
        self.constrRewriteList.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getConstrRewriteList(&self) -> RwLockReadGuard<Vec<ConstrRewriteComponent>> {
        self.constrRewriteList.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getConstrRewriteListMut(&self) -> RefMut<'_, Vec<ConstrRewriteComponent>> {
        self.constrRewriteList.borrow_mut()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getConstrRewriteListMut(&self) -> RwLockWriteGuard<Vec<ConstrRewriteComponent>> {
        self.constrRewriteList.write().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getFunctionalityComponentsList(&self) -> Ref<Vec<ConstrRewriteComponent>> {
        self.functionalityComponentsList.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getFunctionalityComponentsList(&self) -> RwLockReadGuard<Vec<ConstrRewriteComponent>> {
        self.functionalityComponentsList.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getFunctionalityComponentsListMut(&self) -> RefMut<'_, Vec<ConstrRewriteComponent>> {
        self.functionalityComponentsList.borrow_mut()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getFunctionalityComponentsListMut(
        &self,
    ) -> RwLockWriteGuard<Vec<ConstrRewriteComponent>> {
        self.functionalityComponentsList.write().unwrap()
    }
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
        VarType::Int => eg.add(&CHC::IntType(s)),
        VarType::Node => eg.add(&CHC::NodeType(s)),
        VarType::Unknown => {
            todo!()
        }
        VarType::List => eg.add(&CHC::ListType(s)),
        VarType::Bool => todo!(),
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
                // error!("eclass {:?}", $eg.eclass($appId.id).unwrap());
                error!("eclass {:?}", $eg.dumpEClassStr($appId.id));
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

#[cfg(not(feature = "parallelAdd"))]
type FunctionalityComponentsList = Rc<RefCell<Vec<ConstrRewriteComponent>>>;
#[cfg(feature = "parallelAdd")]
type FunctionalityComponentsList = Arc<RwLock<Vec<ConstrRewriteComponent>>>;

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

fn functionalityTransformationApply<'a>(
    functionalityComponentsList: &FunctionalityComponentsList,
    constrRewriteList: &ConstrRewriteList,
    #[cfg(not(feature = "parallelAdd"))] eg: &mut CHCEGraph,
    #[cfg(feature = "parallelAdd")] eg: &'a RwLock<&'a mut CHCEGraph>,
) {
    #[cfg(not(feature = "parallelAdd"))]
    let list = functionalityComponentsList.borrow();

    #[cfg(feature = "parallelAdd")]
    let list = functionalityComponentsList.read().unwrap();

    for components in list.iter() {
        let ConstrRewriteComponent {
            constrAppId,
            constrENode,
            newENodeAppId,
            newENode,
            tag,
        } = components;

        {
            checkNewENode!(newENode, &getEg(eg));
        }

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

            let egRead = getEg(eg);
            let childrenData = egRead.analysis_data(*id);
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

        let varTypes = getAllVarTypesOfENode(&newENode, &getEg(eg));

        {
            let mut egMut = getEgMut(eg);
            for (outputSetsAndChildIdx) in inputToOutputMapping.values() {
                if outputSetsAndChildIdx.len() == 1 {
                    continue;
                }

                let (firstOutputGroup, firstChildIdx) = &outputSetsAndChildIdx[0];
                let outputLen = firstOutputGroup.len();
                for (outputGroup, childIdx) in &outputSetsAndChildIdx[1..] {
                    assert!(outputLen == outputGroup.len());

                    for i in 0..outputLen {
                        let firstVarType = varTypes.get(&firstOutputGroup[i]).unwrap().clone();
                        let firstGroupVar =
                            getVarAppId(firstOutputGroup[i], firstVarType, &mut egMut);
                        let varType = varTypes.get(&outputGroup[i]).unwrap().clone();
                        let var = getVarAppId(outputGroup[i], varType, &mut egMut);

                        let eqId = egMut.add(&CHC::Eq(firstGroupVar, var));
                        newAndChildren.push(AppliedIdOrStar::AppliedId(eqId));
                    }

                    filterOutChildIdx.insert(*childIdx);
                }
            }
        }

        if filterOutChildIdx.len() == 0 {
            continue;
        }

        let mut egMut = getEgMut(eg);

        let mut newUnfoldedChildren: OrderVec<AppliedIdOrStar> = unfoldedChildren
            .iter()
            .enumerate()
            .filter(|(i, _)| !filterOutChildIdx.contains(i))
            .map(|(_, c)| c.clone())
            .collect();

        let (updatedNewENode, newAnd, newAndAppId) = sortNewENode2(
            &syntax,
            &newAndChildren,
            &newUnfoldedChildren,
            #[cfg(not(feature = "parallelAdd"))]
            egMut,
            #[cfg(feature = "parallelAdd")]
            eg,
        );
        let updatedNewENodeAppId = egMut.add(&updatedNewENode.clone());
        checkVarType!(&updatedNewENodeAppId, &egMut);

        checkNewENode!(updatedNewENode, &egMut);

        #[cfg(not(feature = "parallelAdd"))]
        constrRewriteList
            .clone()
            .borrow_mut()
            .push(ConstrRewriteComponent {
                constrAppId: newAndAppId.clone(),
                constrENode: newAnd.clone(),
                newENodeAppId: updatedNewENodeAppId.clone(),
                newENode: updatedNewENode.clone(),
                tag: "from_functionalityTransformation".to_owned(),
            });

        #[cfg(feature = "parallelAdd")]
        constrRewriteList
            .clone()
            .write()
            .unwrap()
            .push(ConstrRewriteComponent {
                constrAppId: newAndAppId.clone(),
                constrENode: newAnd.clone(),
                newENodeAppId: updatedNewENodeAppId.clone(),
                newENode: updatedNewENode.clone(),
                tag: "from_functionalityTransformation".to_owned(),
            });

        egMut.union_justified(
            &newENodeAppId,
            &updatedNewENodeAppId,
            Some("functionalityTransformation".to_owned()),
        );
    }
}

fn functionalityTransformation(
    constrRewriteList: &ConstrRewriteList,
    functionalityComponentsList: &ConstrRewriteList,
) -> CHCRewrite {
    debug!("doing functionalityTransformation");
    let searcher = Box::new(move |eg: &CHCEGraph| -> () {});

    let functionalityComponentsListClone = functionalityComponentsList.clone();
    let constrRewriteListClone = constrRewriteList.clone();
    let applier = Box::new(move |_: (), eg: &mut CHCEGraph| {
        functionalityTransformationApply(
            &functionalityComponentsListClone,
            &constrRewriteListClone,
            #[cfg(not(feature = "parallelAdd"))]
            eg,
            #[cfg(feature = "parallelAdd")]
            &RwLock::new(eg),
        );
        #[cfg(not(feature = "parallelAdd"))]
        functionalityComponentsListClone.borrow_mut().clear();

        #[cfg(feature = "parallelAdd")]
        functionalityComponentsListClone.write().unwrap().clear();
    });

    debug!("done functionalityTransformation");
    RewriteT {
        name: "functionalityTransformation".to_owned(),
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
        eg.canonAppIdsCache(),
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
        eg.add(&syntaxENode)
    };

    let cond = eg.add(&CHC::And(vec![].into()));

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
    bodyAppIds: &Vec<AppliedIdOrStar>,
    eg: &mut CHCEGraph,
) -> CHC {
    let mut aggrAppId: Vec<_> = bodyAppIds.iter().map(|a| a.getAppliedId()).collect();
    aggrAppId.push(condAppId.clone());
    aggrAppId.push(syntaxAppId.clone());
    let aggrAppId = sortAppId(&aggrAppId, true, eg.canonAppIdsCache());

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

pub fn sortNewENode2<'a>(
    syntaxAppId: &AppliedId,
    condChildren: &OrderVec<AppliedIdOrStar>,
    predicateChildren: &OrderVec<AppliedIdOrStar>,
    #[cfg(not(feature = "parallelAdd"))] eg: &mut CHCEGraph,
    #[cfg(feature = "parallelAdd")] eg: &'a RwLock<&'a mut CHCEGraph>,
) -> (CHC, CHC, AppliedId) {
    debug!("doing sortNewENode2");
    let mut aggrAppId: Vec<_> = predicateChildren.iter().map(|a| a.getAppliedId()).collect();
    aggrAppId.extend(condChildren.iter().map(|a| a.getAppliedId()));
    aggrAppId.push(syntaxAppId.clone());
    let aggrAppId = sortAppId(&aggrAppId, true, getEg(eg).canonAppIdsCache());

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
    let condAppId = {
        let mut condENodeForAdd = condENode.clone();
        let mut egMut = getEgMut(eg);
        let bij = egMut.shapeMut(&mut condENodeForAdd);
        egMut.addShape(condENodeForAdd, bij)
    };

    if CHECKS {
        checkDedup(
            condAppId.id,
            &sortedCondChildren.into(),
            &getEg(eg).canonAppIdsCache(),
        )
        .unwrap();
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

fn rebuildENode(enode: &CHC, eg: &CHCEGraph) -> CHC {
    let enode = eg.find_enode(enode);
    let mut enode = enode.sorted(eg.canonAppIdsCache());
    enode.weak_shapeMut();
    enode
}

fn rebuildDoneDefinedList(defineHelper: &DefineHelper, eg: &CHCEGraph) {
    info!(
        "doneDefinedList hits/misses {:?}/{:?}",
        defineHelper.doneDefinedList.getHits(),
        defineHelper.doneDefinedList.getMisses()
    );
    let rebuildDoneDefinedList = {
        let list = &defineHelper.doneDefinedList.getList();
        let originalDoneDefinedListLen = list.len();
        let rebuildDoneDefinedList = BTreeSet::from_iter(list.iter().map(|e| rebuildENode(e, eg)));
        info!(
            "rebuildDoneDefinedList: {originalDoneDefinedListLen:?} -> {:?}",
            rebuildDoneDefinedList.len()
        );
        rebuildDoneDefinedList
    };
    *defineHelper.doneDefinedList.getListMut() = rebuildDoneDefinedList;
}

fn rebuildConstrCheckedCache(unfoldHelper: &UnfoldHelper, eg: &CHCEGraph) {
    info!(
        "constrCheckedCache hits/misses {:?}/{:?}",
        unfoldHelper.constrCheckedCache.getHits(),
        unfoldHelper.constrCheckedCache.getMisses()
    );
    let originalUnsatLen = unfoldHelper.constrCheckedCache.getUnsatCache().len();
    let unsatCacheRebuild = BTreeSet::from_iter(
        unfoldHelper
            .constrCheckedCache
            .getUnsatCache()
            .iter()
            .map(|e| {
                // let e = eg.find_enode(e);
                // let CHC::And(children) = e else {
                //     panic!();
                // };
                // let sortedChildren = sortAppId(
                //     &children.0.iter().map(|x| x.getAppliedId()).collect(),
                //     true,
                //     eg.canonAppIdsCache(),
                // );
                // let mut newE = CHC::And(
                //     sortedChildren
                //         .into_iter()
                //         .map(AppliedIdOrStar::from)
                //         .collect::<Vec<_>>()
                //         .into(),
                // );
                // newE.weak_shapeMut();
                // newE
                rebuildENode(e, eg)
            }),
    );
    info!(
        "rebuildUnsatCache: {originalUnsatLen:?} -> {:?}",
        unsatCacheRebuild.len()
    );
    *unfoldHelper.constrCheckedCache.getUnsatCacheMut() = unsatCacheRebuild;

    let originalSatLen = unfoldHelper.constrCheckedCache.getSatCache().len();
    let satCacheRebuild = BTreeSet::from_iter(
        unfoldHelper
            .constrCheckedCache
            .getSatCache()
            .iter()
            .map(|e| {
                // let e = eg.find_enode(e);
                // let CHC::And(children) = e else {
                //     panic!();
                // };
                // let sortedChildren = sortAppId(
                //     &children.0.iter().map(|x| x.getAppliedId()).collect(),
                //     true,
                //     eg.canonAppIdsCache(),
                // );
                // let mut newE = CHC::And(
                //     sortedChildren
                //         .into_iter()
                //         .map(AppliedIdOrStar::from)
                //         .collect::<Vec<_>>()
                //         .into(),
                // );
                // newE.weak_shapeMut();
                // newE
                rebuildENode(e, eg)
            }),
    );
    info!(
        "rebuildSatCache: {originalSatLen:?} -> {:?}",
        satCacheRebuild.len()
    );
    *unfoldHelper.constrCheckedCache.getSatCacheMut() = satCacheRebuild;
}

fn rebuildCache(unfoldHelper: &UnfoldHelper, defineHelper: &DefineHelper) -> CHCRewrite {
    let unfoldHelper = unfoldHelper.clone();
    let defineHelper = defineHelper.clone();
    let searcher = Box::new(move |eg: &CHCEGraph| -> () {});
    let applier = Box::new(move |_: (), eg: &mut CHCEGraph| {
        if CHECK_UNSAT_CONSTR {
            rebuildConstrCheckedCache(&unfoldHelper, eg);
        }
        rebuildDoneDefinedList(&defineHelper, eg);
    });
    RewriteT {
        name: "rebuildCache".to_owned(),
        searcher,
        applier,
    }
    .into()
}

// TODO: swapping unfold and define creates some error which should not be
pub fn getAllRewrites(rewriteList: RewriteList, options: RewriteOption) -> Vec<CHCRewrite> {
    let RewriteList {
        unfoldHelper,
        constrRewriteList,
        functionalityComponentsList,
        defineHelper,
    } = &rewriteList;
    // define-fold, unfold
    let mut rewrites = vec![
        rebuildCache(&unfoldHelper, &defineHelper),
        unfold(&unfoldHelper, &constrRewriteList),
    ];

    // constraint until saturation
    if options.doConstraintRewrite {
        // TODO: can be a while loop?
        rewrites.push(constraintRewrite(&rewriteList));
        rewrites.push(functionalityTransformation(
            &constrRewriteList,
            &functionalityComponentsList,
        ));
        rewrites.push(constraintRewrite(&rewriteList));
        rewrites.push(functionalityTransformation(
            &constrRewriteList,
            &functionalityComponentsList,
        ));
        rewrites.push(constraintRewrite(&rewriteList));
    }

    rewrites.extend([
        defineUnfoldFold(&unfoldHelper, &defineHelper, &constrRewriteList, options),
        trueToAnd(),
        eqSwap(),
    ]);

    rewrites
}
