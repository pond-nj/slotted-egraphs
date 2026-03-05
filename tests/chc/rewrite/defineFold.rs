use super::*;
use crate::*;

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
                let group = vec![i, j + i + 1];
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

pub fn defineUnfoldFold(
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
            // TODO: can we actually parallelize this?
            for origNewENode in enodesList {
                let origENodeShape = origNewENode.weak_shape().0;
                // check if do this already
                let mut processedDefinedListClone = processedDefinedListClone.borrow_mut();
                if processedDefinedListClone.contains(&origENodeShape) {
                    continue;
                }
                processedDefinedListClone.insert(origENodeShape.clone());

                let CHC::New(origSyntaxAppId, origConstrAppId, bodyAppIds) = &origNewENode else {
                    continue;
                };

                checkNewENode!(origNewENode, eg);

                let mut mergeVarTypes: BTreeMap<Slot, VarType> =
                    getAllVarTypesOfENode(&origNewENode, eg);

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
                                None,
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
                        trace!("fold to {defineAppId:?}");
                        trace!("original body {bodyAppIds:?}");
                        trace!("positions {positions:?}");
                        let mut foldedBodyAppIds = vec![];
                        for (idx, c) in bodyAppIds.iter().enumerate() {
                            if idx == *replaceAt {
                                // TODO: defineAppId must be mapped to originalENode namespace
                                foldedBodyAppIds
                                    .push(AppliedIdOrStar::AppliedId(defineAppId.clone()));
                            }

                            if positions.contains(&idx) {
                                continue;
                            }
                            foldedBodyAppIds.push(c.clone());
                        }
                        trace!("foldedBodyAppIds {foldedBodyAppIds:?}");
                        debug!("origNewENode {origNewENode:?}");
                        let foldedNewENode = sortNewENode1(
                            origSyntaxAppId,
                            origConstrAppId,
                            &foldedBodyAppIds.into(),
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
