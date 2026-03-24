use super::*;
use crate::*;

#[derive(Default, Clone)]
pub struct DoneDefinedList {
    pub list: Rc<RefCell<BTreeSet<CHC>>>,
    pub hits: Rc<RefCell<usize>>,
    pub misses: Rc<RefCell<usize>>,
}

#[derive(Default, Clone)]
pub struct DefineCache {
    pub doneDefinedList: DoneDefinedList,
    pub newDefineMap: Rc<RefCell<BTreeMap<FoldPattern, AppliedId>>>,
}

struct DefineInfo {
    syntax: Vec<Slot>,
    newBody: Vec<AppliedId>,
    positions: Vec<usize>,
    tag: String,
}

fn doADTDefine(
    childAppIds: &Vec<AppliedIdOrStar>,
    mergeVarTypes: &BTreeMap<Slot, VarType>,
    eclassId: Id,
    syntaxAndNewBody: &mut Vec<DefineInfo>,
) {
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

fn doPairingDefine(
    childAppIds: &Vec<AppliedIdOrStar>,
    eclassId: Id,
    syntaxAndNewBody: &mut Vec<DefineInfo>,
) {
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

fn prepareDefines(
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
        doADTDefine(childAppIds, mergeVarTypes, eclassId, syntaxAndNewBody);
    }

    // pairing
    // only support two predicates now
    if options.doPairingDefine {
        doPairingDefine(childAppIds, eclassId, syntaxAndNewBody);
    }
}

fn unfoldNewDefine(
    syntax: &Vec<Slot>,
    sortedNewBody: &Vec<AppliedIdOrStar>,
    sortedToBeFoldShape: Vec<AppliedIdOrStar>,
    map: &SlotMap,
    tag: String,
    mergeVarTypes: &BTreeMap<Slot, VarType>,
    newDefineMap: &Rc<RefCell<BTreeMap<FoldPattern, AppliedId>>>,
    unfoldList: &Rc<RefCell<UnfoldList>>,
    constrCheckedCache: &ConstrCheckedCache,
    constrRewriteListCopy: &Rc<RefCell<ConstrRewriteList>>,
    eg: &mut CHCEGraph,
) -> AppliedId {
    // define
    let definedENode = {
        let mapInverse = map.inverse();
        let mut syntaxVarsNormalized: Vec<_> = syntax.into_iter().map(|s| mapInverse[*s]).collect();
        // sort according to order in weakshape (ordered by nauty-trace)
        syntaxVarsNormalized.sort();
        let syntaxVars: Vec<_> = syntaxVarsNormalized.into_iter().map(|s| map[s]).collect();

        let syntaxAppId = {
            let children = syntaxVars
                .into_iter()
                .map(|s| getVarAppId(s, mergeVarTypes[&s].clone(), eg))
                .collect::<Vec<_>>();
            let syntaxENode = CHC::PredSyntax(children.into());
            eg.add(&syntaxENode)
        };

        let cond = eg.add(&CHC::And(vec![].into()));
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
        constrCheckedCache,
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
                &unfoldList,
                &Rc::clone(&constrRewriteListCopy),
                eg,
            ));
        }
    }

    let first = newComposeAppIds.first().unwrap();
    for newComposeAppId in newComposeAppIds[1..].iter() {
        eg.union_justified(first, newComposeAppId, Some("define_unfold".to_owned()));
    }

    assert!(unfoldList.borrow().len() > 0);

    let saveAppId = eg.find_applied_id(first).apply_slotmap(&map.inverse());
    debug!("defineMap {saveAppId:?} <- {sortedToBeFoldShape:?}");
    newDefineMap
        .borrow_mut()
        .insert(sortedToBeFoldShape, saveAppId);

    eg.find_applied_id(first)
}

fn doFolding(
    origNewENodeAppId: &AppliedId,
    defineAppId: &AppliedId,
    bodyAppIds: &Vec<AppliedIdOrStar>,
    positions: &Vec<usize>,
    origSyntaxAppId: &AppliedId,
    origConstrAppId: &AppliedId,
    eg: &mut CHCEGraph,
) {
    let replaceAt = positions.first().unwrap();
    let mut foldedBodyAppIds = vec![];
    for (idx, c) in bodyAppIds.iter().enumerate() {
        if idx == *replaceAt {
            // TODO: defineAppId must be mapped to originalENode namespace
            foldedBodyAppIds.push(AppliedIdOrStar::AppliedId(defineAppId.clone()));
        }

        if positions.contains(&idx) {
            continue;
        }
        foldedBodyAppIds.push(c.clone());
    }
    let foldedNewENode = sortNewENode1(
        origSyntaxAppId,
        origConstrAppId,
        &foldedBodyAppIds.into(),
        eg,
    );
    let foldedAppId = eg.add(&foldedNewENode);
    eg.analysis_data_mut(foldedAppId.id)
        .predNames
        .insert(format!(
            "folded_{}_with_{}",
            origNewENodeAppId, defineAppId.id
        ));
    eg.union_justified(&origNewENodeAppId, &foldedAppId, Some("fold".to_owned()));
}

pub fn defineApply(
    unfoldHelper: &UnfoldHelper,
    defineCache: &DefineCache,
    constrRewriteListCopy: &Rc<RefCell<ConstrRewriteList>>,
    options: RewriteOption,
    eg: &mut CHCEGraph,
) {
    let DefineCache {
        doneDefinedList: DoneDefinedList { list, hits, misses },
        newDefineMap,
    } = defineCache;

    let UnfoldHelper {
        unfoldList,
        constrCheckedCache,
    } = unfoldHelper;

    let ids = eg.ids();
    let idsLen = ids.len();
    for (i, eclassId) in ids.into_iter().enumerate() {
        info!("doing define {i}/{idsLen}");
        if i == idsLen / 2 {
            break;
        }
        let eclassId = eg.find_id(eclassId);
        let origNewENodeAppId = eg.mk_identity_applied_id(eclassId);

        let enodesList = eg.enodes(origNewENodeAppId.id);
        let enodesListLen = enodesList.len();
        // TODO: can we actually parallelize this?
        for (j, origNewENode) in enodesList.into_iter().enumerate() {
            info!("doing define {i}/{idsLen} {j}/{enodesListLen}");
            let origENodeShape = origNewENode.weak_shape().0;
            // check if do this already
            // TODO: I think we need refresh the cache here?
            let mut doneDefinedList = list.borrow_mut();
            if doneDefinedList.contains(&origENodeShape) {
                *hits.borrow_mut() += 1;
                continue;
            }
            *misses.borrow_mut() += 1;
            doneDefinedList.insert(origENodeShape.clone());

            let CHC::New(origSyntaxAppId, origConstrAppId, bodyAppIds) = &origNewENode else {
                continue;
            };

            checkNewENode!(origNewENode, eg);

            let mut mergeVarTypes: BTreeMap<Slot, VarType> =
                getAllVarTypesOfENode(&origNewENode, eg);

            // divide body into blocks
            let mut syntaxAndNewBody: Vec<DefineInfo> = vec![];
            prepareDefines(
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
                let sortedNewBody: Vec<AppliedIdOrStar> =
                    sortAppId(&newBody, true, eg.canonAppIdsCache())
                        .into_iter()
                        .map(|x| AppliedIdOrStar::AppliedId(x))
                        .collect();
                // 0 -> $f
                let (sortedToBeFoldShape, map) = weakShapeAppIds(&sortedNewBody);

                let mut savedDefineAppId =
                    if let Some(savedFolded) = newDefineMap.borrow().get(&sortedToBeFoldShape) {
                        trace!("get savedfolded");
                        Some(savedFolded.clone().apply_slotmap(&map))
                    } else {
                        None
                    };

                if savedDefineAppId.is_none() {
                    savedDefineAppId = Some(unfoldNewDefine(
                        &syntax,
                        &sortedNewBody,
                        sortedToBeFoldShape,
                        &map,
                        tag.clone(),
                        &mergeVarTypes,
                        &newDefineMap,
                        &unfoldList,
                        &constrCheckedCache,
                        &constrRewriteListCopy,
                        eg,
                    ));
                }

                let defineAppId = savedDefineAppId.unwrap();

                eg.analysis_data_mut(defineAppId.id)
                    .predNames
                    .insert(format!("define_from_{}_{}", origNewENodeAppId.id, tag));

                // vv folding vv
                if options.doFolding {
                    doFolding(
                        &origNewENodeAppId,
                        &defineAppId,
                        bodyAppIds,
                        &positions,
                        origSyntaxAppId,
                        origConstrAppId,
                        eg,
                    )
                }
            }
        }
    }
}

// TODO: refactor this function
pub fn defineUnfoldFold(
    unfoldHelper: &UnfoldHelper,
    defineCache: &DefineCache,
    constrRewriteList: &Rc<RefCell<ConstrRewriteList>>,
    options: RewriteOption,
) -> CHCRewrite {
    let defineCacheClone = (*defineCache).clone();
    let searcher = Box::new(move |eg: &CHCEGraph| -> () {});
    let unfoldHelperClone = unfoldHelper.clone();
    let constrRewriteListClone = Rc::clone(constrRewriteList);
    let applier = Box::new(move |substs: (), eg: &mut CHCEGraph| {
        defineApply(
            &unfoldHelperClone,
            &defineCacheClone,
            &constrRewriteListClone,
            options.clone(),
            eg,
        )
    });

    RewriteT {
        name: "define".to_owned(),
        searcher,
        applier,
    }
    .into()
}
