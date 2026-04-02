#[cfg(feature = "parallelAdd")]
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;

use super::*;
use crate::*;

#[cfg(not(feature = "parallelAdd"))]
#[derive(Default, Clone)]
pub struct DoneDefinedList {
    pub list: Rc<RefCell<BTreeSet<CHC>>>,
    pub hits: Rc<RefCell<usize>>,
    pub misses: Rc<RefCell<usize>>,
}

#[cfg(feature = "parallelAdd")]
#[derive(Default, Clone)]
pub struct DoneDefinedList {
    pub list: Arc<RwLock<BTreeSet<CHC>>>,
    pub hits: Arc<RwLock<usize>>,
    pub misses: Arc<RwLock<usize>>,
}

impl DoneDefinedList {
    #[cfg(not(feature = "parallelAdd"))]
    pub fn getList(&self) -> Ref<'_, BTreeSet<CHC>> {
        self.list.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getList(&self) -> RwLockReadGuard<BTreeSet<CHC>> {
        self.list.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getListMut(&self) -> RefMut<'_, BTreeSet<CHC>> {
        self.list.borrow_mut()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getListMut(&self) -> RwLockWriteGuard<BTreeSet<CHC>> {
        self.list.write().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getHits(&self) -> Ref<'_, usize> {
        self.hits.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getHits(&self) -> RwLockReadGuard<usize> {
        self.hits.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getHitsMut(&self) -> RefMut<'_, usize> {
        self.hits.borrow_mut()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getHitsMut(&self) -> RwLockWriteGuard<usize> {
        self.hits.write().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getMisses(&self) -> Ref<'_, usize> {
        self.misses.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getMisses(&self) -> RwLockReadGuard<usize> {
        self.misses.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getMissesMut(&self) -> RefMut<'_, usize> {
        self.misses.borrow_mut()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getMissesMut(&self) -> RwLockWriteGuard<usize> {
        self.misses.write().unwrap()
    }
}

#[cfg(not(feature = "parallelAdd"))]
#[derive(Default, Clone, Debug)]
pub struct DefineStats {
    pub adtDefine: Rc<RefCell<usize>>,
    pub pairingDefine: Rc<RefCell<usize>>,
}

#[cfg(feature = "parallelAdd")]
#[derive(Default, Clone, Debug)]
pub struct DefineStats {
    pub adtDefine: Arc<RwLock<usize>>,
    pub pairingDefine: Arc<RwLock<usize>>,
}

impl DefineStats {
    #[cfg(not(feature = "parallelAdd"))]
    pub fn getAdtDefine(&self) -> Ref<'_, usize> {
        self.adtDefine.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getAdtDefine(&self) -> RwLockReadGuard<'_, usize> {
        self.adtDefine.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getAdtDefineMut(&self) -> RefMut<'_, usize> {
        self.adtDefine.borrow_mut()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getAdtDefineMut(&self) -> RwLockWriteGuard<usize> {
        self.adtDefine.write().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getPairingDefine(&self) -> Ref<'_, usize> {
        self.pairingDefine.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getPairingDefine(&self) -> RwLockReadGuard<'_, usize> {
        self.pairingDefine.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getPairingDefineMut(&self) -> RefMut<'_, usize> {
        self.pairingDefine.borrow_mut()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getPairingDefineMut(&self) -> RwLockWriteGuard<usize> {
        self.pairingDefine.write().unwrap()
    }
}

#[derive(Default, Clone)]
pub struct DefineHelper {
    pub doneDefinedList: DoneDefinedList,
    #[cfg(not(feature = "parallelAdd"))]
    pub newDefineMap: Rc<RefCell<BTreeMap<FoldPattern, AppliedId>>>,
    #[cfg(feature = "parallelAdd")]
    pub newDefineMap: Arc<RwLock<BTreeMap<FoldPattern, AppliedId>>>,
    pub stats: DefineStats,
}

impl DefineHelper {
    #[cfg(not(feature = "parallelAdd"))]
    pub fn getNewDefineMap(&self) -> Ref<'_, BTreeMap<FoldPattern, AppliedId>> {
        self.newDefineMap.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getNewDefineMap(&self) -> RwLockReadGuard<BTreeMap<FoldPattern, AppliedId>> {
        self.newDefineMap.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getNewDefineMapMut(&self) -> RefMut<'_, BTreeMap<FoldPattern, AppliedId>> {
        self.newDefineMap.borrow_mut()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getNewDefineMapMut(&self) -> RwLockWriteGuard<BTreeMap<FoldPattern, AppliedId>> {
        self.newDefineMap.write().unwrap()
    }
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
    stats: &DefineStats,
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

        *stats.getAdtDefineMut() += 1;
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
    stats: &DefineStats,
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
            *stats.getPairingDefineMut() += 1;
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
    syntaxAndNewBody: &mut Vec<DefineInfo>,
    eg: &CHCEGraph,
    stats: &DefineStats,
) {
    // ADT
    let CHC::New(origSyntaxAppId, origConstrAppId, childAppIds) = &origNewENode else {
        panic!();
    };

    if options.doADTDefine {
        doADTDefine(
            childAppIds,
            mergeVarTypes,
            eclassId,
            syntaxAndNewBody,
            stats,
        );
    }

    // pairing
    // only support two predicates now
    if options.doPairingDefine {
        doPairingDefine(childAppIds, eclassId, syntaxAndNewBody, stats);
    }
}

fn unfoldNewDefine<'a>(
    syntax: &Vec<Slot>,
    sortedNewBody: &Vec<AppliedIdOrStar>,
    sortedToBeFoldShape: Vec<AppliedIdOrStar>,
    map: &SlotMap,
    tag: String,
    mergeVarTypes: &BTreeMap<Slot, VarType>,
    newDefineMap: &mut BTreeMap<FoldPattern, AppliedId>,
    unfoldHelper: &UnfoldHelper,
    constrCheckedCache: &ConstrCheckedCache,
    constrRewriteListCopy: &ConstrRewriteList,
    #[cfg(not(feature = "parallelAdd"))] eg: &mut CHCEGraph,
    #[cfg(feature = "parallelAdd")] eg: &'a RwLock<&'a mut CHCEGraph>,
) -> AppliedId {
    // define
    let definedENode = {
        let mapInverse = map.inverse();
        let mut syntaxVarsNormalized: Vec<_> = syntax.into_iter().map(|s| mapInverse[*s]).collect();
        // sort according to order in weakshape (ordered by nauty-trace)
        syntaxVarsNormalized.sort();
        let syntaxVars: Vec<_> = syntaxVarsNormalized.into_iter().map(|s| map[s]).collect();

        let egMut = &mut getEgMut(eg);
        let syntaxAppId = {
            let children = syntaxVars
                .into_iter()
                .map(|s| getVarAppId(s, mergeVarTypes[&s].clone(), egMut))
                .collect::<Vec<_>>();
            let syntaxENode = CHC::PredSyntax(children.into());
            egMut.add(&syntaxENode)
        };

        let cond = egMut.add(&CHC::And(vec![].into()));
        CHC::New(syntaxAppId, cond, sortedNewBody.clone().into())
    };

    // unfold
    let mut composeUnfoldRecipes = vec![];
    {
        prepareUnfold(
            None,
            0,
            &vec![].into(),
            &AppliedId::null(),
            &AppliedId::null(),
            &definedENode,
            &mut composeUnfoldRecipes,
            constrCheckedCache,
            &getEg(eg),
        );
    }

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
                unfoldHelper,
                &constrRewriteListCopy.clone(),
                #[cfg(not(feature = "parallelAdd"))]
                eg,
                #[cfg(feature = "parallelAdd")]
                &eg,
            ));
        }
    }

    let mut egMut = getEgMut(eg);
    let first = newComposeAppIds.first().unwrap();
    for newComposeAppId in newComposeAppIds[1..].iter() {
        egMut.union_justified(first, newComposeAppId, Some("define_unfold".to_owned()));
    }

    assert!(unfoldHelper.getUnfoldList().len() > 0);

    let saveAppId = egMut.find_applied_id(first).apply_slotmap(&map.inverse());
    debug!("defineMap {saveAppId:?} <- {sortedToBeFoldShape:?}");
    newDefineMap.insert(sortedToBeFoldShape, saveAppId);

    egMut.find_applied_id(first)
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
    eg.updateAnalysisData(foldedAppId.id, |data| {
        data.predNames.insert(format!(
            "folded_{}_with_{}",
            origNewENodeAppId, defineAppId.id
        ));
    });

    eg.union_justified(&origNewENodeAppId, &foldedAppId, Some("fold".to_owned()));
}

pub fn defineApply(
    unfoldHelper: &UnfoldHelper,
    defineHelper: &DefineHelper,
    constrRewriteListCopy: &ConstrRewriteList,
    options: RewriteOption,
    eg: &mut CHCEGraph,
) {
    let stats = &defineHelper.stats;

    let UnfoldHelper {
        unfoldList,
        constrCheckedCache,
    } = unfoldHelper;

    let ids = eg.ids();
    let idsLen = ids.len();

    #[cfg(not(feature = "parallelAdd"))]
    let iter = ids.into_iter().enumerate().collect::<Vec<_>>().into_iter();
    #[cfg(feature = "parallelAdd")]
    let iter = ids
        .into_iter()
        .enumerate()
        .collect::<Vec<_>>()
        .into_par_iter();

    let eg = getLockEg(eg);

    iter.for_each(|(i, eclassId)| {
        info!("doing define {i}/{idsLen}");

        let (enodesList, origNewENodeAppId) = {
            let egRead = getEg(eg);
            let eclassId = egRead.find_id(eclassId);
            let origNewENodeAppId = egRead.mk_identity_applied_id(eclassId);

            (egRead.enodes(origNewENodeAppId.id), origNewENodeAppId)
        };
        let enodesListLen = enodesList.len();
        for (j, origNewENode) in enodesList.into_iter().enumerate() {
            info!(
                "define stats adtDefine/pairingDefine {:?}/{:?}",
                stats.getAdtDefine(),
                stats.getPairingDefine()
            );
            info!("doing define {i}/{idsLen} {j}/{enodesListLen}");
            let origENodeShape = origNewENode.weak_shape().0;
            // check if do this already
            // TODO: I think we need refresh the cache here?
            {
                let mut doneDefinedList = defineHelper.doneDefinedList.getListMut();
                if doneDefinedList.contains(&origENodeShape) {
                    *defineHelper.doneDefinedList.getHitsMut() += 1;
                    continue;
                }
                *defineHelper.doneDefinedList.getMissesMut() += 1;
                doneDefinedList.insert(origENodeShape.clone());
            }

            let CHC::New(origSyntaxAppId, origConstrAppId, bodyAppIds) = &origNewENode else {
                continue;
            };

            let mut mergeVarTypes = {
                let egRead = getEg(eg);
                checkNewENode!(origNewENode, &egRead);

                getAllVarTypesOfENode(&origNewENode, &egRead)
            };

            // divide body into blocks
            let mut syntaxAndNewBody: Vec<DefineInfo> = vec![];
            {
                prepareDefines(
                    &origNewENode,
                    &mergeVarTypes,
                    &options,
                    eclassId,
                    &mut syntaxAndNewBody,
                    &getEg(eg),
                    stats,
                );
            }

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
                let sortedNewBody: Vec<AppliedIdOrStar> = {
                    sortAppId(&newBody, true, getEg(eg).canonAppIdsCache())
                        .into_iter()
                        .map(|x| AppliedIdOrStar::AppliedId(x))
                        .collect()
                };
                // 0 -> $f
                let (sortedToBeFoldShape, map) = weakShapeAppIds(&sortedNewBody);

                let mut savedDefineAppId = if let Some(savedFolded) =
                    defineHelper.getNewDefineMap().get(&sortedToBeFoldShape)
                {
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
                        &mut defineHelper.getNewDefineMapMut(),
                        unfoldHelper,
                        &constrCheckedCache,
                        &constrRewriteListCopy,
                        eg,
                    ));
                }

                let defineAppId = savedDefineAppId.unwrap();

                {
                    let mut egMut = getEgMut(eg);
                    egMut.updateAnalysisData(defineAppId.id, |data| {
                        data.predNames
                            .insert(format!("define_from_{}_{}", origNewENodeAppId.id, tag));
                    });
                }

                // vv folding vv
                if options.doFolding {
                    doFolding(
                        &origNewENodeAppId,
                        &defineAppId,
                        bodyAppIds,
                        &positions,
                        origSyntaxAppId,
                        origConstrAppId,
                        &mut getEgMut(eg),
                    )
                }
            }
        }
    });
}

// TODO: refactor this function
pub fn defineUnfoldFold(
    unfoldHelper: &UnfoldHelper,
    defineHelper: &DefineHelper,
    constrRewriteList: &ConstrRewriteList,
    options: RewriteOption,
) -> CHCRewrite {
    let defineCacheClone = (*defineHelper).clone();
    let searcher = Box::new(move |eg: &CHCEGraph| -> () {});
    let unfoldHelperClone = unfoldHelper.clone();
    let constrRewriteListClone = constrRewriteList.clone();
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
