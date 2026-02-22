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

fn getAnyAndChildren(appId: &AppliedId, eg: &CHCEGraph) -> OrderVec<AppliedIdOrStar> {
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

macro_rules! checkVarType {
    ($appId: expr, $eg: expr) => {
        if CHECKS {
            let eclassData = $eg.analysis_data($appId.id);
            if $appId.len() != 0 && eclassData.varTypes.len() == 0 {
                error!("varTypes len 0");
                error!("appId {:?}", $appId);
                error!("eclass {:?}", $eg.eclass($appId.id).unwrap());
                assert!(eclassData.varTypes.len() > 0);
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
macro_rules! checkNewENode {
    ($enode: expr) => {
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
                warn!("alert enode = {:?}", $enode.weak_shape().0);
            }
        }
    };
}

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
            warn!(
                "alert syntax = {:?}, cond = {:?}, children = {:?}",
                $syntax, $cond, $children
            );
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
// recipe for creating unfolded ENode
// contributes to one CHC rule
pub struct UnfoldRecipe {
    syntax1: AppliedId,
    mergeAndChildren: OrderVec<AppliedIdOrStar>,
    unfoldedChildren: OrderVec<AppliedIdOrStar>,
    new2EClass: AppliedId,
}

#[derive(Debug)]
struct ComposeUnfoldRecipe {
    // keeps multiple choices
    // e.g. we want to unfold p <- q
    // and q has 3 rules:
    // 1) q <- r1 equivalent to q <- r2,
    // 2) q <- s1 equivalent to q <- s2,
    // 3) q <- t1 equivalent to q <- t2
    // then we can unfold into
    // p <- ri, p <- sj, p <- tk using any combination of i, j, k in {1, 2}
    // Hence, Vec<Vec<UnfoldRecipe>> is
    // {{result from using q <- r1, result from using q <- r2},
    // {result from using q <- s1, result from using q <- s2},
    // {result from using q <- t1, result from using q <- t2}}
    unfoldRecipe: Vec<Vec<UnfoldRecipe>>,
    excludeIdx: usize,
    compose1Children: OrderVec<AppliedId>,
    rootId: AppliedId,
    compose2Id: AppliedId,
    new1UnfoldIdx: usize,
    new1EClass: AppliedId,
}

#[derive(Debug, Clone, Ord, PartialEq, PartialOrd, Eq)]
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
    tag: String,
}

type FoldPattern = Vec<AppliedIdOrStar>;

#[derive(Default)]
pub struct RewriteList {
    unfoldList: Rc<RefCell<UnfoldList>>,
    constrRewriteList: Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    functionalityComponentsList: Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    definedList: Rc<RefCell<BTreeSet<CHC>>>,
    newDefineMap: Rc<RefCell<BTreeMap<FoldPattern, AppliedId>>>,
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

type UnfoldList = DedupVec<(UnfoldListComponent)>;

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

    let new1Children = match &toBeUnfolded.newENodeShape {
        CHC::New(_, _, new1Children) => new1Children,
        _ => panic!(),
    };

    if new1Children.len() == 0 {
        debug!("skip toBeUnfolded {toBeUnfolded:#?}");
        return;
    }

    let mut unfoldListCopy = Rc::clone(unfoldList);
    unfoldListCopy.borrow_mut().push(toBeUnfolded);
}

fn functionalityTransformation(
    constrRewriteList: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    functionalityComponentsList: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
) -> CHCRewrite {
    info!("doing functionalityTransformation");
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

            checkNewENode!(newENode);

            let CHC::New(syntax, andAppId, unfoldedChildren) = newENode else {
                panic!();
            };

            let CHC::And(andChildren) = constrENode else {
                panic!();
            };

            // input to output mapping
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

            let getVarType = |toSlot, appId: AppliedId, egraph: &CHCEGraph| {
                let varTypes = &egraph.analysis_data(appId.id).varTypes;
                let fromSlot = appId.m.inverse()[toSlot];
                varTypes.get(&fromSlot).unwrap().clone()
            };

            for (outputSetsAndChildIdx) in inputToOutputMapping.values() {
                if outputSetsAndChildIdx.len() == 1 {
                    continue;
                }

                let (firstOutputGroup, firstChildIdx) = &outputSetsAndChildIdx[0];
                let outputLen = firstOutputGroup.len();
                for (outputGroup, childIdx) in &outputSetsAndChildIdx[1..] {
                    assert!(outputLen == outputGroup.len());

                    for i in 0..outputLen {
                        let firstVarType = getVarType(
                            firstOutputGroup[i],
                            unfoldedChildren[*firstChildIdx].getAppliedId(),
                            eg,
                        );
                        let firstGroupVar = getVarAppId(firstOutputGroup[i], firstVarType, eg);
                        let varType = getVarType(
                            outputGroup[i],
                            unfoldedChildren[*childIdx].getAppliedId(),
                            eg,
                        );
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
                sortNewENode2(syntax, &newAndChildren, &newUnfoldedChildren, eg);
            let updatedNewENodeAppId = eg.add(updatedNewENode.clone());
            checkVarType!(&updatedNewENodeAppId, eg);

            checkNewENode!(updatedNewENode);

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

    info!("done functionalityTransformation");
    RewriteT {
        name: "functionalityTransformation".to_owned(),
        searcher: searcher,
        applier: applier,
    }
    .into()
}

// note: i1, compose1Children, composeAppId, new1EClass can be null if called from define
fn unfoldSearchInternal(
    i1: usize,
    compose1Children: &OrderVec<AppliedId>,
    composeAppId: &AppliedId,
    new1EClass: &AppliedId,
    new1: &CHC,
    composeUnfoldReceipt: &mut Vec<ComposeUnfoldRecipe>,
    eg: &CHCEGraph,
) {
    let (syntax1, cond1, new1Children) = match new1.clone() {
        CHC::New(syntax1, cond1, new1Children) => (syntax1, cond1, new1Children),
        _ => panic!(),
    };

    let and1Children = getAnyAndChildren(&cond1, eg);
    trace!("unfoldSearch new1 {new1:?}");
    for (new1UnfoldIdx, compose2Id) in new1Children.iter().enumerate() {
        let compose2Id = compose2Id.getAppliedId();
        let compose2Vec = eg.enodes_applied(&compose2Id);
        trace!("unfoldSearch compose2Vec {compose2Vec:?}");
        assert!(
            compose2Vec.iter().any(|c| matches!(c, CHC::Compose(..))),
            "a class with ComposeInit does not have Compose, {}",
            compose2Id
        );
        for compose2 in compose2Vec {
            if let CHC::ComposeInit(..) = compose2 {
                continue;
            }

            let compose2 = eg.find_enode(&compose2);
            trace!("unfoldSearch compose2 {compose2:?}");
            let CHC::Compose(compose2Children) = compose2 else {
                panic!();
            };

            let mut unfoldedENodesRecipe: Vec<Vec<UnfoldRecipe>> = vec![];
            for new2EClass in compose2Children.iter() {
                let new2EClass = new2EClass.getAppliedId();
                let mut fromThisEClassRecipe: Vec<UnfoldRecipe> = vec![];
                let new2Vec = eg.enodes_applied(&new2EClass);
                assert!(new2Vec.len() > 0);
                for new2 in new2Vec {
                    let tmp2 = new2.clone();
                    checkNewENode!(tmp2);
                    let CHC::New(syntax2, cond2, new2Children) = new2 else {
                        panic!();
                    };

                    let and2Children = getAnyAndChildren(&cond2, eg);

                    let mut unfoldedChildren = new1Children.clone();

                    let mut tmpVec = unfoldedChildren;
                    let mut unfoldedChildren = vec![];
                    for i in 0..tmpVec.len() {
                        if i == new1UnfoldIdx {
                            // replace this position with unfolded (new2) children
                            unfoldedChildren.extend(new2Children.clone());
                        } else {
                            unfoldedChildren.push(tmpVec[i].clone());
                        }
                    }

                    // must be sorted first before dedup, dedup only remove consecutive duplicates

                    let mut mergeAndChildren = and1Children.clone();
                    mergeAndChildren.extend(and2Children);

                    checkNewENodeComponent!(
                        syntax1,
                        mergeAndChildren.clone(),
                        unfoldedChildren.clone()
                    );

                    // prepare for rewrite.
                    // cannot rewrite here because this is searcher only.
                    // separate search and rewrte.
                    fromThisEClassRecipe.push(UnfoldRecipe {
                        syntax1: syntax1.clone(),
                        mergeAndChildren,
                        unfoldedChildren: unfoldedChildren.into(),
                        new2EClass: new2EClass.clone(),
                    });
                }
                if (fromThisEClassRecipe.len() == 0) {
                    error!("fromThisEClassRecipe is empty");
                    error!("eclass {}: {:?}", new2EClass.id, eg.eclass(new2EClass.id));
                    assert!(fromThisEClassRecipe.len() > 0);
                }
                unfoldedENodesRecipe.push(fromThisEClassRecipe);
            }

            let x = ComposeUnfoldRecipe {
                unfoldRecipe: unfoldedENodesRecipe,
                excludeIdx: i1,
                compose1Children: compose1Children.clone(),
                rootId: composeAppId.clone(),
                compose2Id: compose2Id.clone(),
                new1UnfoldIdx,
                new1EClass: new1EClass.clone(),
            };

            composeUnfoldReceipt.push(x);
        }
    }

    assert!(composeUnfoldReceipt.len() > 0);
}

fn unfoldSearch(
    unfoldListCopy: &Rc<RefCell<UnfoldList>>,
    eg: &CHCEGraph,
) -> Vec<ComposeUnfoldRecipe> {
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

        // TODO: change this to get
        let compose1 = eg.getExactENodeInEGraph(&composeShape);

        let compose1Children = match compose1 {
            CHC::Compose(compose1Children) => compose1Children,
            _ => panic!(),
        };

        let mut compose1Children: OrderVec<AppliedId> = compose1Children
            .into_iter()
            .map(|appId| {
                let AppliedIdOrStar::AppliedId(appId) = appId else {
                    panic!();
                };
                appId
            })
            .collect();
        // compose1Children.sort();
        let composeUnfoldRecipeLenBefore = composeUnfoldReceipt.len();

        for (i1, new1EClass) in compose1Children.iter().enumerate() {
            if new1EClass.id != eg.find_applied_id(&newEClassAppId).id {
                debug!("skip new1EClass {:?}", new1EClass);
                continue;
            }

            let new1 = eg
                .getExactENodeInEClass(&newENodeShape, &new1EClass.id)
                .apply_slotmap_partial(&new1EClass.m);

            checkNewENode!(new1);

            unfoldSearchInternal(
                i1,
                &compose1Children,
                &composeAppId,
                new1EClass,
                &new1,
                &mut composeUnfoldReceipt,
                eg,
            );
        }

        if composeUnfoldReceipt.len() == composeUnfoldRecipeLenBefore {
            panic!("skip this recipe");
        }
    }

    assert!(eg.total_number_of_nodes() == oldEgSize);
    composeUnfoldReceipt
}

#[derive(PartialEq, Eq, Debug)]
pub enum UnfoldOpType {
    UnfoldMerge, //merge is for normal unfold, which will unfold and merge with the old compose
    UnfoldCreateOnly, //create is for unfold occur in define, which will only create unfolded nodes, there's no old compose.
}

fn unfoldApplyInternal(
    composeRecipe: &ComposeUnfoldRecipe,
    unfoldListCopy2: &Rc<RefCell<UnfoldList>>,
    constrRewriteListCopy: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    createOrMerge: UnfoldOpType, //if true, will merge with information from composeRecipe, if false, will create
    eg: &mut CHCEGraph,
) -> Vec<AppliedId> {
    let ComposeUnfoldRecipe {
        unfoldRecipe,
        excludeIdx,
        compose1Children,
        rootId,
        compose2Id,
        new1UnfoldIdx,
        new1EClass,
    } = composeRecipe;

    trace!(
        "unfolding {compose2Id} (index {new1UnfoldIdx}) in {} under {rootId}",
        new1EClass.id
    );
    trace!("root compose eclass {:?}", eg.eclass(rootId.id));
    trace!("new1EClass eclass {:?}", eg.eclass(new1EClass.id));
    trace!("used eclass {:?}", eg.eclass(compose2Id.id));

    if createOrMerge == UnfoldOpType::UnfoldCreateOnly {
        assert_eq!(compose1Children, &vec![].into());
        assert_eq!(rootId, &AppliedId::null());
        assert_eq!(excludeIdx, &0);
        assert_eq!(new1EClass, &AppliedId::null());
    }

    let mut createdComposeAppIds = vec![];
    // TODO: should we change this to iter?

    let unfoldRecipeCombs = combination(&unfoldRecipe);
    if unfoldRecipeCombs.len() == 0 {
        error!("unfoldRecipeCombs is empty");
        error!("unfoldRecipe {unfoldRecipe:#?}");
        assert!(unfoldRecipeCombs.len() > 0);
    }
    for unfoldRecipeComb in unfoldRecipeCombs {
        let mut childrenComb = vec![];
        let mut createdNewENodes = vec![];
        for unfoldRecipe in unfoldRecipeComb {
            let UnfoldRecipe {
                syntax1,
                mut mergeAndChildren,
                mut unfoldedChildren,
                new2EClass,
            } = unfoldRecipe;

            let (unfoldedENode, mergeAnd, mergeAndAppId) =
                sortNewENode2(&syntax1, &mergeAndChildren, &unfoldedChildren, eg);

            checkVarType!(&mergeAndAppId, eg);

            match createOrMerge {
                UnfoldOpType::UnfoldCreateOnly => {
                    eg.analysis_data_mut(mergeAndAppId.id)
                        .predNames
                        .insert(format!(
                        "and_from_unfold_define_{compose2Id}_{new1UnfoldIdx}_using_{new2EClass}",
                    ));
                }
                UnfoldOpType::UnfoldMerge => {
                    eg.analysis_data_mut(mergeAndAppId.id)
                        .predNames
                        .insert(format!(
                            "and_from_unfold_{compose2Id}_{new1UnfoldIdx}_in_{}_using_{new2EClass}",
                            new1EClass.id
                        ));
                }
            }

            checkNewENode!(unfoldedENode);

            let unfoldedENodeId = eg.add(unfoldedENode.clone());
            eg.shrink_slots(&unfoldedENodeId, &syntax1.slots(), ());

            let tag = if createOrMerge == UnfoldOpType::UnfoldMerge {
                format!(
                    "unfold_{compose2Id}_{new1UnfoldIdx}_in_{}_using_{new2EClass}",
                    new1EClass.id
                )
            } else {
                format!("define_unfold_{compose2Id}_{new1UnfoldIdx}_using_{new2EClass}")
            };

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

            createdNewENodes.push((unfoldedENodeId.clone(), unfoldedENode.clone()));

            debug!("adding unfoldedENode {tag} {unfoldedENodeId:?}");
            eg.analysis_data_mut(unfoldedENodeId.id)
                .predNames
                .insert(tag);
            childrenComb.push(unfoldedENodeId);
        }

        let mut composeAppId = None;
        let mut composeShape = None;
        match createOrMerge {
            // merge with the existsing before
            UnfoldOpType::UnfoldMerge => {
                let mut unfoldedComposeChildren = compose1Children.clone();
                unfoldedComposeChildren.remove(*excludeIdx);
                unfoldedComposeChildren.extend(childrenComb);
                let unfoldedComposeChildren: Vec<_> = sortAppId(&unfoldedComposeChildren)
                    .iter()
                    .map(|x| AppliedIdOrStar::AppliedId(x.clone()))
                    .collect();
                let composeENode = CHC::Compose(unfoldedComposeChildren.clone().into());

                let unfoldedCompose = eg.add(composeENode.clone());
                debug!(
                    "UnfoldOpType::UnfoldMerge added composeENode {:?}",
                    composeENode.weak_shape().0
                );

                // for p in permute_iter(&unfoldedComposeChildren) {
                //     let pBare = p.iter().map(|x| x.getAppliedId()).collect::<Vec<_>>();
                //     let pSorted = sortAppId(&pBare);
                //     assert!(
                //         unfoldedComposeChildren
                //             == pSorted
                //                 .iter()
                //                 .map(|x| AppliedIdOrStar::AppliedId(x.clone()))
                //                 .collect::<Vec<_>>()
                //     );

                //     let permutedComposeShape = CHC::Compose(p).weak_shape().0;
                //     if permutedComposeShape != composeENode.weak_shape().0 {
                //         let res = eg.lookup(&permutedComposeShape);
                //         if !res.is_none() {
                //             if res.clone().unwrap().id != unfoldedCompose.id {
                //                 println!("eg {eg:?}");
                //                 println!(
                //                     "lookup id {:?}, added id {:?}",
                //                     res.unwrap(),
                //                     unfoldedCompose.id
                //                 );
                //                 println!("permutedComposeShape {permutedComposeShape:?}");
                //                 println!("composeENode {:?}", composeENode.weak_shape().0);
                //                 assert!(false);
                //             }
                //         }
                //     }
                // }

                checkVarType!(&unfoldedCompose, eg);
                eg.union_justified(&rootId, &unfoldedCompose, Some("unfold".to_owned()));

                composeAppId = Some(unfoldedCompose.clone());
                composeShape = Some(composeENode);
                createdComposeAppIds.push(unfoldedCompose);
            }
            // just create unfold node
            UnfoldOpType::UnfoldCreateOnly => {
                // let childrenComb: Vec<_> = childrenComb
                //     .into_iter()
                //     .map(|appId| AppliedIdOrStar::AppliedId(appId))
                //     .collect();
                let childrenComb = sortAppId(&childrenComb);
                let childrenComb: Vec<_> = childrenComb
                    .into_iter()
                    .map(|appId| AppliedIdOrStar::AppliedId(appId))
                    .collect();
                composeShape = Some(CHC::Compose(childrenComb.clone().into()));
                debug!(
                    "UnfoldOpType::UnfoldMerge added composeENode {:?}",
                    composeShape.clone().unwrap().weak_shape().0
                );

                composeAppId = Some(eg.add(composeShape.clone().unwrap()));
                // for p in permute_iter(&childrenComb) {
                //     let pBare = p.iter().map(|x| x.getAppliedId()).collect::<Vec<_>>();
                //     let pSorted = sortAppId(&pBare);
                //     assert!(
                //         childrenComb
                //             == pSorted
                //                 .iter()
                //                 .map(|x| AppliedIdOrStar::AppliedId(x.clone()))
                //                 .collect::<Vec<_>>()
                //     );

                //     let permutedComposeShape = CHC::Compose(p).weak_shape().0;
                //     if permutedComposeShape != composeShape.clone().unwrap().weak_shape().0 {
                //         let res = eg.lookup(&permutedComposeShape);
                //         if !res.is_none() {
                //             if res.clone().unwrap().id != composeAppId.clone().unwrap().id {
                //                 println!("eg {eg:?}");
                //                 println!(
                //                     "lookup id {:?}, added id {:?}",
                //                     res.unwrap(),
                //                     composeAppId.clone().unwrap().id
                //                 );
                //                 println!("permutedComposeShape {permutedComposeShape:?}");
                //                 println!(
                //                     "composeShape {:?}",
                //                     composeShape.clone().unwrap().weak_shape().0
                //                 );
                //                 assert!(false);
                //             }
                //         }
                //     }
                // }

                createdComposeAppIds.push(composeAppId.clone().unwrap());
            }
        };

        for (enodeId, enode) in createdNewENodes {
            addToUnfoldList(
                &unfoldListCopy2,
                UnfoldListComponent {
                    composeAppId: composeAppId.clone().unwrap(),
                    composeShape: composeShape.clone().unwrap(),
                    newEClassAppId: enodeId,
                    newENodeShape: enode,
                },
            );
        }
    }

    assert!(createdComposeAppIds.len() > 0);
    createdComposeAppIds.into()
}

fn unfoldApply(
    unfoldListCopy2: &Rc<RefCell<UnfoldList>>,
    composeRecipes: Vec<ComposeUnfoldRecipe>,
    constrRewriteListCopy: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    eg: &mut CHCEGraph,
) {
    Rc::clone(&unfoldListCopy2).borrow_mut().clear();
    for composeRecipe in composeRecipes.iter() {
        unfoldApplyInternal(
            composeRecipe,
            unfoldListCopy2,
            constrRewriteListCopy,
            UnfoldOpType::UnfoldMerge,
            eg,
        );
    }
}

// H <- A, B, C unfolding using A one time, B one time, C one time
// H <- A', B, C
// H <- A, B', C
// H <- A, B, C'
fn unfold(
    unfoldList: &Rc<RefCell<UnfoldList>>,
    constrRewriteList: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
) -> CHCRewrite {
    let unfoldListCopy = Rc::clone(unfoldList);
    let constrRewriteListCopy = Rc::clone(constrRewriteList);
    let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<ComposeUnfoldRecipe> {
        unfoldSearch(&unfoldListCopy, eg)
    });

    let unfoldListCopy2 = Rc::clone(unfoldList);
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

// TODO: caching of processed node here?
// TODO: this function takes a long time
// expand eq rewrite, X = Y, X = Z -> X = Y, X = Z, Y = Z
// expand eq rewrite, X = node(a, l, r), Y = node(a, l, r) -> X = Y, X = node(a, l, r), Y = node(a, l, r)
pub fn expandEqRewrite(
    constrAppId: &AppliedId,
    constrENode: &CHC,
    originalNewENode: &CHC,
    eg: &mut CHCEGraph,
) -> CHC {
    info!("doing expandEqRewrite");
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

    eg.union_justified(
        constrAppId,
        &newConstraintAppId,
        Some("expandEq".to_owned()),
    );

    info!("done expandEqRewrite");
    return newConstraint;
}

// TODO: this function is taking a long time
// constructor eq rewrite, node(x, l, r) = node(x', l', r') -> x = x', l = l', r = r'
pub fn constructorEqRewrite(
    constrAppId: &AppliedId,
    constrENode: &CHC,
    originalNewENode: &CHC,
    eg: &mut CHCEGraph,
) -> CHC {
    info!("doing constructorEqRewrite");
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

    checkVarType!(&newConstraintAppId, eg);
    eg.union_justified(
        &constrAppId,
        &newConstraintAppId,
        Some("constructorEqRewrite".to_owned()),
    );

    info!("done constructorEqRewrite");
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
    info!("doing dedupFromEqRewrite");
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

    let updatedNewAppId = eg.add(updatedNew.clone());

    eg.union_justified(
        &newENodeAppId,
        &updatedNewAppId,
        Some("dedupFromEqRewrite".to_owned()),
    );

    info!("done dedupFromEqRewrite");
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

            checkNewENode!(newENode);

            // expand eq rewrite, X = Y, X = Z -> X = Y, X = Z, Y = Z
            // expand eq rewrite, X = node(a, l, r), Y = node(a, l, r) -> X = Y, X = node(a, l, r), Y = node(a, l, r)
            let constrENode = expandEqRewrite(constrAppId, constrENode, newENode, eg);

            // constructor eq rewrite, node(x, l, r) = node(x', l', r') -> x = x', l = l', r = r'
            let constrENode = constructorEqRewrite(constrAppId, &constrENode, newENode, eg);

            // deduplicate constraint a = a2, a = a1, l = l1, r = r1, t = node(a, l, r), t = node(a1, l1, r1)
            // -> a = a, l = l, r = r, t = node(a, l, r), t = node(a, l, r)
            // -> t = node(a, l, r)
            // deduplicate predicate calls a = a1, P(a, z), P(a1, z) -> P(a, z)
            let (newConstraint, updatedNewENode) =
                dedupFromEqRewrite(constrAppId, &constrENode, newENodeAppId, newENode, eg);

            checkNewENode!(updatedNewENode);

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
    let aggrAppId = sortAppId(&aggrAppId);

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
    let aggrAppId = sortAppId(&aggrAppId);

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

    let condENode = CHC::And(sortedCondChildren.into());
    let condAppId = eg.add(condENode.clone());

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

fn defineUnfoldFold(
    unfoldList: &Rc<RefCell<UnfoldList>>,
    processedDefinedList: &Rc<RefCell<BTreeSet<CHC>>>,
    newDefineMap: &Rc<RefCell<BTreeMap<FoldPattern, AppliedId>>>,
    constrRewriteList: &Rc<RefCell<Vec<ConstrRewriteComponent>>>,
    doFolding: bool,
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
                let mut processedDefinedListClone = processedDefinedListClone.borrow_mut();
                // check if do this already
                if processedDefinedListClone.contains(&origENodeShape) {
                    continue;
                }
                processedDefinedListClone.insert(origENodeShape.clone());

                let CHC::New(origSyntaxAppId, origConstrAppId, childAppIds) = &origNewENode else {
                    continue;
                };

                checkNewENode!(origNewENode);

                // TODO0: try change to rootData instead of mergeVarTypes
                let mut varToChildIdx: BTreeMap<Slot, Vec<usize>> = BTreeMap::default();
                let mut aggrVarTypes: BTreeMap<Slot, VarType> = BTreeMap::default();

                for idx in 0..childAppIds.len() {
                    let appId = childAppIds[idx].getAppliedId();
                    for s in appId.slots() {
                        varToChildIdx.entry(s).or_insert(vec![]).push(idx);
                    }

                    let childrenVarTypes = &eg.analysis_data(appId.id).varTypes;
                    aggrVarTypes.extend(
                        appId
                            .m
                            .clone()
                            .into_iter()
                            .map(|(from, to)| (to, *childrenVarTypes.get(&from).unwrap())),
                    );
                }

                // let mut rootData = eg.analysis_data(rootAppId.id).varTypes.clone();
                let mergeVarTypes = aggrVarTypes;

                let mut unionfind: QuickUnionUf<UnionBySize> =
                    QuickUnionUf::<UnionBySize>::new(childAppIds.len());
                let mut hasNonBasicVar = vec![false; childAppIds.len()];

                for (var, childrenIndx) in &varToChildIdx {
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

                // for each group/sharing block, define new chc
                for (_, mut group) in groupMap {
                    group.sort();
                    let mut basicVars: BTreeSet<Slot> = BTreeSet::default();
                    for i in &group {
                        let appId = childAppIds[*i].getAppliedId();
                        for var in appId.slots() {
                            if !isNonBasicVar(&mergeVarTypes[&var]) {
                                basicVars.insert(var);
                            }
                        }
                    }

                    // TODO: not sure why this is this
                    if basicVars.len() == 0 {
                        warn!("basicVars is empty");
                        warn!("origNewENode {:?}", origNewENode);
                        warn!("group {:?}", group);
                    }

                    let mut children: Vec<_> =
                        group.iter().map(|i| childAppIds[*i].clone()).collect();

                    // let oldLen = eg.total_number_of_nodes();

                    let toBeFold = group
                        .iter()
                        .map(|idx| childAppIds[*idx].getAppliedId())
                        .collect::<Vec<_>>();
                    let sortedToBeFold: Vec<AppliedIdOrStar> = sortAppId(&toBeFold)
                        .into_iter()
                        .map(|x| AppliedIdOrStar::AppliedId(x))
                        .collect();
                    // 0 -> $f
                    let (sortedToBeFoldShape, map) = weakShapeAppIds(&sortedToBeFold);

                    let mut newDefineMapClone = Rc::clone(&newDefineMapClone);
                    let mut newDefineMapClone = newDefineMapClone.borrow_mut();
                    let defineAppId =
                        if let Some(savedFolded) = newDefineMapClone.get(&sortedToBeFoldShape) {
                            trace!("get savedfolded");
                            savedFolded.clone().apply_slotmap(&map)
                        } else {
                            let definedENode = {
                                let mapInverse = map.inverse();
                                let mut syntaxVars: Vec<_> =
                                    basicVars.into_iter().map(|s| mapInverse[s]).collect();
                                syntaxVars.sort();
                                let syntaxVars: Vec<_> =
                                    syntaxVars.into_iter().map(|s| map[s]).collect();

                                let syntaxAppId = {
                                    let children = syntaxVars
                                        .into_iter()
                                        .map(|s| getVarAppId(s, mergeVarTypes[&s].clone(), eg))
                                        .collect::<Vec<_>>();
                                    let syntaxENode = CHC::PredSyntax(children.into());
                                    eg.add(syntaxENode)
                                };

                                let cond = eg.add(CHC::And(vec![].into()));

                                CHC::New(syntaxAppId, cond, sortedToBeFold.clone().into())
                            };

                            let mut composeUnfoldReceipt = vec![];
                            unfoldSearchInternal(
                                0,
                                &vec![].into(),
                                &AppliedId::null(),
                                &AppliedId::null(),
                                &definedENode,
                                &mut composeUnfoldReceipt,
                                eg,
                            );

                            // TODO: it should be more than one
                            // let mut newComposeAppIds = vec![];
                            // for composeRecipe in composeUnfoldReceipt.iter() {
                            //     newComposeAppIds.extend(unfoldApplyInternal(
                            //         composeRecipe,
                            //         &unfoldListClone,
                            //         &Rc::clone(&constrRewriteListCopy),
                            //         UnfoldOpType::UnfoldCreateOnly,
                            //         eg,
                            //     ));
                            // }
                            if composeUnfoldReceipt.len() > 1 {
                                // printENode(&definedENode, eg);
                                // println!("composeUnfoldReceipt {:#?}", composeUnfoldReceipt);
                                // assert!(composeUnfoldReceipt.len() == 1);
                                warn!("composeUnfoldReceipt len > 1 but also use the first one");
                                warn!("composeUnfoldReceipt {:?}", composeUnfoldReceipt);
                            }
                            let newComposeAppIds = unfoldApplyInternal(
                                &composeUnfoldReceipt[0],
                                &unfoldListClone,
                                &Rc::clone(&constrRewriteListCopy),
                                UnfoldOpType::UnfoldCreateOnly,
                                eg,
                            );

                            // if (newComposeAppIds.is_empty()) {
                            //     println!("unfold result is empty");
                            //     println!("composeRecipes {:?}");
                            // }
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
                        .insert(format!("define_from_{}", origNewENodeAppId.id));

                    // vv folding vv
                    if doFolding {
                        let replaceAt = group.first().unwrap();
                        debug!("sortedToBeFold {sortedToBeFold:?}");
                        debug!("fold group to {defineAppId:?}");
                        let mut restChildAppIds = vec![];
                        for (idx, c) in childAppIds.iter().enumerate() {
                            if idx == *replaceAt {
                                // TODO: defineAppId must be mapped to originalENode namespace
                                restChildAppIds
                                    .push(AppliedIdOrStar::AppliedId(defineAppId.clone()));
                            }

                            if group.contains(&idx) {
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
pub fn getAllRewrites(
    rewriteList: RewriteList,
    doConstraintRewrite: bool,
    doFolding: bool,
) -> Vec<CHCRewrite> {
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
    if doConstraintRewrite {
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
            doFolding,
        ),
        trueToAnd(),
        eqSwap(),
    ]);

    rewrites
}
