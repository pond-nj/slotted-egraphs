use super::*;
use crate::*;
use derive_more::derive;
use log::debug;
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;
use tracing_subscriber::filter::combinator::And;
use union_find::{QuickUnionUf, UnionBySize, UnionFind};

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
    new1EClass: AppliedId,
}

#[derive(Debug, Clone)]
pub struct UnfoldListComponent {
    composeAppId: AppliedId,
    composeShape: CHC,
    newEClassAppId: AppliedId,
    newENodeShape: CHC,
}

impl UnfoldListComponent {
    pub fn getShape(&self) -> (UnfoldListComponent, SlotMap) {
        let (composeShape, m) = self.composeShape.weak_shape();

        (
            UnfoldListComponent {
                composeAppId: self.composeAppId.apply_slotmap(&m.inverse()),
                composeShape,
                newEClassAppId: self.newEClassAppId.apply_slotmap(&m.inverse()),
                newENodeShape: self.newENodeShape.apply_slotmap(&m.inverse()),
            },
            m,
        )
    }
}

type UnfoldList = Vec<(UnfoldListComponent)>;

// TODO unfold list, list of ENodes waiting to be unfolded
// add new unfolded ENode to the Unfold list
// unfold every clause in the body at most once in unfold one rewrite

// Fold list should also be from the unfold list

// 1) composeAppId, 2) NewEClass AppliedId, 3) New ENode shape
// fn unfold(unfoldList: &Rc<RefCell<UnfoldList>>) -> CHCRewrite {
//     let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<ComposeUnfoldRecipe> {
//         let rootPat = Pattern::parse("(compose <*0>)").unwrap();
//         let rootMatches = ematch_all(eg, &rootPat);
//         // (compose1 <(new1 syntax1 cond1 <(compose2 <new2 syntax2>)>)>)
//         let mut composeUnfoldReceipt = vec![];
//         for (compose1Children, rootId1) in rootMatches {
//             let rootId = lookupPattern(eg, &rootPat, &compose1Children).unwrap();
//             assert!(rootId1 == rootId.id);
//             let mut compose1Children: Vec<AppliedId> = compose1Children
//                 .iter()
//                 .map(|(s, appId)| appId.clone())
//                 .collect();
//             compose1Children.sort();
//             for (i1, new1EClass) in compose1Children.iter().enumerate() {
//                 for new1 in eg.enodes_applied(new1EClass) {
//                     if let CHC::Interface(..) = new1 {
//                         continue;
//                     }

//                     let CHC::New(syntax1, cond1, new1Children) = new1 else {
//                         panic!();
//                     };

//                     let and1Children = getAnyAndChildren(&cond1, eg);
//                     for (i2, compose2Id) in new1Children.iter().enumerate() {
//                         let compose2Id = compose2Id.getAppliedId();
//                         for compose2 in eg.enodes_applied(&compose2Id) {
//                             if let CHC::Init(..) = compose2 {
//                                 continue;
//                             }

//                             let CHC::Compose(compose2Children) = compose2 else {
//                                 panic!();
//                             };

//                             let mut unfoldedENodesRecipe: Vec<Vec<UnfoldRecipe>> = vec![];
//                             for new2EClass in compose2Children.iter() {
//                                 let new2EClass = new2EClass.getAppliedId();
//                                 let mut fromThisEClassRecipe: Vec<UnfoldRecipe> = vec![];
//                                 for new2 in eg.enodes_applied(&new2EClass) {
//                                     if let CHC::Interface(..) = new2 {
//                                         continue;
//                                     }

//                                     let CHC::New(syntax2, cond2, new2Children) = new2 else {
//                                         panic!();
//                                     };

//                                     let and2Children = getAnyAndChildren(&cond2, eg);

//                                     let mut unfoldedChildren = new1Children.clone();
//                                     unfoldedChildren.remove(i2);
//                                     // 2
//                                     unfoldedChildren.extend(new2Children.clone());

//                                     let mut mergeAndChildren = and1Children.clone();
//                                     mergeAndChildren.extend(and2Children);

//                                     fromThisEClassRecipe.push((
//                                         syntax1.clone(),
//                                         mergeAndChildren,
//                                         unfoldedChildren,
//                                         new2EClass.clone(),
//                                     ));
//                                 }
//                                 unfoldedENodesRecipe.push(fromThisEClassRecipe);
//                             }

//                             composeUnfoldReceipt.push(ComposeUnfoldRecipe {
//                                 unfoldRecipe: unfoldedENodesRecipe,
//                                 exclude: i1,
//                                 compose1Children: compose1Children.clone(),
//                                 rootId: rootId.clone(),
//                                 compose2Id: compose2Id.clone(),
//                                 new1EClass: new1EClass.clone(),
//                             });
//                         }
//                     }
//                 }
//             }
//         }

//         composeUnfoldReceipt
//     });
//     let applier = Box::new(
//         move |composeRecipes: Vec<ComposeUnfoldRecipe>, eg: &mut CHCEGraph| {
//             for composeRecipe in composeRecipes {
//                 let ComposeUnfoldRecipe {
//                     unfoldRecipe,
//                     exclude,
//                     compose1Children,
//                     rootId,
//                     compose2Id,
//                     new1EClass,
//                 } = composeRecipe;
//                 let mut toBeUnion = vec![];
//                 // this loops takes a long time, around 1sec per iter
//                 for unfoldRecipeComb in combination(unfoldRecipe) {
//                     let mut childrenComb = vec![];
//                     let start = Instant::now(); // Record the start time
//                                                 // this one takes around half the time of the whole loop
//                     let (_, time1) = time(|| {
//                         for (syntax1, mut mergeAndChildren, mut unfoldedChildren, new2EClass) in
//                             unfoldRecipeComb
//                         {
//                             mergeAndChildren.sort();
//                             let mergeAnd = eg.add(CHC::And(mergeAndChildren));
//                             eg.analysis_data_mut(mergeAnd.id).predNames.insert(format!(
//                                 "and_from_unfold_{compose2Id}_in_{new1EClass}_using_{new2EClass}"
//                             ));
//                             unfoldedChildren.sort();
//                             let unfoldedENode = CHC::New(syntax1, mergeAnd, unfoldedChildren);
//                             let unfoldedENodeId = eg.add(unfoldedENode);
//                             eg.analysis_data_mut(unfoldedENodeId.id)
//                                 .predNames
//                                 .insert(format!(
//                                     "unfold_{compose2Id}_in_{new1EClass}_using_{new2EClass}"
//                                 ));
//                             childrenComb.push(unfoldedENodeId);
//                         }
//                     });

//                     let (_, time2) = time(|| {
//                         let mut unfoldedComposeChildren = compose1Children.clone();
//                         unfoldedComposeChildren.remove(exclude);
//                         unfoldedComposeChildren.extend(childrenComb);
//                         unfoldedComposeChildren.sort();
//                         let unfoldedComposeChildren = unfoldedComposeChildren
//                             .into_iter()
//                             .map(|appId| AppliedIdOrStar::AppliedId(appId.clone()))
//                             .collect();
//                         let unfoldedCompose = eg.add(CHC::Compose(unfoldedComposeChildren));
//                         toBeUnion.push(unfoldedCompose);
//                     });
//                 }
//                 // if there's no union here, it ends very fast
//                 for x in toBeUnion {
//                     eg.union(&rootId, &x);
//                 }
//             }
//         },
//     );
//     RewriteT {
//         name: "unfold".to_owned(),
//         searcher: searcher,
//         applier: applier,
//     }
//     .into()
// }

fn unfold(unfoldList: &Rc<RefCell<UnfoldList>>) -> CHCRewrite {
    let unfoldListCopy = Rc::clone(unfoldList);
    let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<ComposeUnfoldRecipe> {
        let mut composeUnfoldReceipt = vec![];
        for toBeUnfolded in Rc::clone(&unfoldListCopy).borrow().iter() {
            let (toBeUnfolded, m) = toBeUnfolded.getShape();
            debug!("unfold: get toBeUnfolded {toBeUnfolded:#?}");
            let UnfoldListComponent {
                composeAppId,
                composeShape,
                newEClassAppId,
                newENodeShape,
            } = toBeUnfolded;

            let compose1 = eg.getNode(&composeAppId, &composeShape);
            // let compose1 = composeShape;
            // let compose1 = eg.find_enode(&composeShape);
            debug!("compose Eclass {:?}", eg.eclass(composeAppId.id));
            debug!("composeAppId {:?}", composeAppId);
            debug!("get compose1 {:?}", compose1);
            debug!("compose1Shape{:?}", composeShape);
            debug!("findCompose1 {:?}", eg.find_enode(&composeShape));

            if eg.find_enode(&composeShape) != compose1 {
                debug!(
                    "look here {:?} != {:?}",
                    eg.find_enode(&composeShape),
                    compose1
                );
            }
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
            for (i1, new1EClass) in compose1Children.iter().enumerate() {
                // TODO: the problem is here
                if eg.find_applied_id(new1EClass) != eg.find_applied_id(&newEClassAppId) {
                    debug!(
                        "unfold: new1EClass {:?} != {:?}",
                        eg.find_applied_id(new1EClass),
                        eg.find_applied_id(&newEClassAppId)
                    );
                    continue;
                }

                debug!("unfold: new1EClass {new1EClass:?}");
                let new1 = eg.getNode(&new1EClass, &newENodeShape);
                // let new1 = newENodeShape.clone();
                // let new1 = eg.find_enode(&newENodeShape);
                debug!("get new1 {new1:?}");
                debug!("new1Shape {newENodeShape:?}");

                let CHC::New(syntax1, cond1, new1Children) = new1 else {
                    panic!();
                };

                let and1Children = getAnyAndChildren(&cond1, eg);
                for (i2, compose2Id) in new1Children.iter().enumerate() {
                    let compose2Id = compose2Id.getAppliedId();
                    for compose2 in eg.enodes_applied(&compose2Id) {
                        if let CHC::Init(..) = compose2 {
                            continue;
                        }

                        let CHC::Compose(compose2Children) = compose2 else {
                            panic!();
                        };

                        let mut unfoldedENodesRecipe: Vec<Vec<UnfoldRecipe>> = vec![];
                        for new2EClass in compose2Children.iter() {
                            let new2EClass = new2EClass.getAppliedId();
                            debug!(
                                "new1Eclass {:?} new2EClassId {:?}, composeAppId {:?}",
                                new1EClass.id, new2EClass.id, composeAppId.id
                            );
                            let mut fromThisEClassRecipe: Vec<UnfoldRecipe> = vec![];
                            for new2 in eg.enodes_applied(&new2EClass) {
                                if let CHC::Interface(..) = new2 {
                                    continue;
                                }

                                let CHC::New(syntax2, cond2, new2Children) = new2 else {
                                    panic!();
                                };

                                let and2Children = getAnyAndChildren(&cond2, eg);

                                let mut unfoldedChildren = new1Children.clone();
                                debug!("unfoldedChildren1 {:?}", unfoldedChildren);
                                unfoldedChildren.remove(i2);
                                // 2
                                unfoldedChildren.extend(new2Children.clone());
                                debug!("unfoldedChildren {:?}", unfoldedChildren);

                                let mut mergeAndChildren = and1Children.clone();
                                mergeAndChildren.extend(and2Children);

                                fromThisEClassRecipe.push(UnfoldRecipe {
                                    syntax1: syntax1.clone(),
                                    mergeAndChildren: mergeAndChildren,
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
                            new1EClass: new1EClass.clone(),
                        };

                        composeUnfoldReceipt.push(x);
                    }
                }
            }
        }

        debug!("unfold search ret {composeUnfoldReceipt:#?}");
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
                    new1EClass,
                } = composeRecipe;
                let mut toBeUnion = vec![];
                // this loops takes a long time, around 1sec per iter
                for unfoldRecipeComb in combination(&unfoldRecipe) {
                    let mut childrenComb = vec![];
                    let start = Instant::now(); // Record the start time
                                                // this one takes around half the time of the whole loop
                    let mut createdENodes = vec![];
                    let (_, time1) = time(|| {
                        for unfoldRecipe in unfoldRecipeComb {
                            debug!("unfoldRecipe {unfoldRecipe:#?}");
                            let UnfoldRecipe {
                                syntax1,
                                mut mergeAndChildren,
                                mut unfoldedChildren,
                                new2EClass,
                            } = unfoldRecipe;

                            mergeAndChildren.sort();
                            let mergeAnd = eg.add(CHC::And(mergeAndChildren));
                            eg.analysis_data_mut(mergeAnd.id).predNames.insert(format!(
                                "and_from_unfold_{compose2Id}_in_{new1EClass}_using_{new2EClass}"
                            ));
                            unfoldedChildren.sort();
                            let unfoldedENode = CHC::New(syntax1, mergeAnd, unfoldedChildren);
                            debug!("adding unfoldedENode {unfoldedENode:?}");
                            let unfoldedENodeId = eg.add(unfoldedENode.clone());
                            createdENodes.push((unfoldedENodeId.clone(), unfoldedENode));
                            debug!("unfoldedENodeId {unfoldedENodeId:?}");
                            debug!("adding unfold enode unfold_{compose2Id}_in_{new1EClass}_using_{new2EClass}");
                            eg.analysis_data_mut(unfoldedENodeId.id)
                                .predNames
                                .insert(format!(
                                    "unfold_{compose2Id}_in_{new1EClass}_using_{new2EClass}"
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
                        debug!("adding composeENode {composeENode:?}");
                        debug!("to be union with {:?}", rootId);
                        let unfoldedCompose = eg.add(composeENode.clone());
                        toBeUnion.push(unfoldedCompose.clone());

                        for (enodeId, enode) in createdENodes {
                            let next = UnfoldListComponent {
                                composeAppId: unfoldedCompose.clone(),
                                composeShape: composeENode.clone(),
                                newEClassAppId: enodeId,
                                newENodeShape: enode,
                            };

                            debug!("pusing to unfoldList {next:#?}");

                            Rc::clone(&unfoldListCopy2).borrow_mut().push(next);
                        }
                    });
                }

                for x in toBeUnion {
                    debug!("union {:?}", eg.eclass(x.id));
                    debug!("with {:?}", eg.eclass(rootId.id));
                    eg.union_justified(&rootId, &x, Some("unfold".to_owned()));
                }
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

// TODO: only define from a list?
fn defineFromSharingBlock(unfoldList: &Rc<RefCell<UnfoldList>>) -> CHCRewrite {
    let pat = Pattern::parse("(new ?syntax ?cond <*1>)").unwrap();
    let patClone = pat.clone();
    let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<Subst> {
        ematch_all(eg, &patClone).into_iter().map(|s| s.0).collect()
    });
    let unfoldListClone = Rc::clone(unfoldList);
    let applier = Box::new(move |substs: Vec<Subst>, eg: &mut CHCEGraph| {
        for subst in substs {
            let rootAppId = pattern_subst(eg, &pat, &subst);

            let origENode = eg
                .getExactENodeInEGraph(&constructENodefromPatternSubst(eg, &pat, &subst).unwrap());

            // TODO0: try change to rootData instead of mergeVarTypes
            let mut rootData = eg.analysis_data(rootAppId.id).varTypes.clone();
            let mut varToChildIndx: HashMap<Slot, Vec<usize>> = HashMap::default();
            let mut mergeVarTypes: HashMap<Slot, VarType> = HashMap::default();
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
            let mut groupMap = HashMap::<usize, Vec<usize>>::default();
            for i in 0..unionfind.size() {
                if hasNonBasicVar[i] {
                    let leader = unionfind.find(i);
                    groupMap.entry(leader).or_insert(vec![]).push(i);
                }
            }

            // for each group, define new chc
            for (_, group) in groupMap {
                let mut basicVars: HashSet<Slot> = HashSet::default();
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

                let dummyEnode = CHC::New(
                    id("(pred <>)", eg),
                    id("(and <>)", eg),
                    children
                        .clone()
                        .into_iter()
                        .map(|a| AppliedIdOrStar::AppliedId(a.clone()))
                        .collect(),
                );
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

                let oldLen = eg.total_number_of_nodes();
                // TODO: change counter to local variable
                let counter = G_COUNTER.load(Ordering::SeqCst);

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

                let itf = id(
                    &format!(
                        "(interface define_from_{}_{} {syntax} 2)",
                        rootAppId.id, counter
                    ),
                    eg,
                );
                eg.union(&newENodeAppId, &itf);
                G_COUNTER.store(counter + 1, Ordering::SeqCst);

                let newENodeShape = newENode.weak_shape().0;
                let composeEnode =
                    CHC::Compose(vec![AppliedIdOrStar::AppliedId(newENodeAppId.clone())]);
                let composeShape = composeEnode.weak_shape().0;
                let composeAppId = eg.add(composeEnode);

                let unfoldListComponent = UnfoldListComponent {
                    composeAppId: composeAppId,
                    composeShape: composeShape,
                    newEClassAppId: newENodeAppId,
                    newENodeShape: newENodeShape,
                };

                println!("pushing to unfoldList {unfoldListComponent:#?}");

                Rc::clone(&unfoldListClone)
                    .borrow_mut()
                    .push(unfoldListComponent);
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

pub fn getAllRewrites(unfoldList: &Rc<RefCell<UnfoldList>>) -> Vec<CHCRewrite> {
    vec![
        unfold(unfoldList),
        defineFromSharingBlock(unfoldList),
        trueToAnd(),
    ]
}
