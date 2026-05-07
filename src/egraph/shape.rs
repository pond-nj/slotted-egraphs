use std::cell::{Ref, RefMut};

use log::info;
use std::io::{self, Write};

use super::*;

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    pub fn canonAppIdsCache(&self) -> &CanonAppIdsCache {
        &self._canonAppIdsCache
    }

    pub fn orig_shape(&self, e: &L) -> (L, Bijection) {
        let (pnode, bij) = self.proven_shape(e);
        if self.find_enode(&e) != *e {
            warn!("shape {e:?} -> {:?} {:?}", pnode.elem, bij);
            warn!("find_enode {e:?} -> {:?}", self.find_enode(&e));
        }
        (pnode.elem, bij)
    }

    #[cfg(not(feature = "newShape"))]
    pub fn shape(&self, e: &L) -> (L, Bijection) {
        let (pnode, bij) = self.proven_shape(e);
        if self.find_enode(&e) != *e {
            warn!("shape {e:?} -> {:?} {:?}", pnode.elem, bij);
            warn!("find_enode {e:?} -> {:?}", self.find_enode(&e));
        }
        (pnode.elem, bij)
    }

    fn checkPermsWithAppIds(
        &self,
        appIds: &Vec<&AppliedId>,
        allPerms: &BTreeMap<AppliedId, Vec<ProvenPerm>>,
    ) {
        for appId in appIds.iter() {
            let perms = &allPerms[appId];
            for p in perms {
                assert_eq!(
                    p.elem.keys_set(),
                    appId.key_slots(),
                    "{:?} {appId:?} {p:?}",
                    self.dumpEClassStr(appId.id)
                );
                assert_eq!(
                    p.elem.values_set(),
                    appId.key_slots(),
                    "{:?} {appId:?} {p:?}",
                    self.dumpEClassStr(appId.id)
                );
            }
        }
    }

    fn getAppIdsToPerm(&self, appIds: &Vec<&AppliedId>) -> BTreeMap<AppliedId, Vec<ProvenPerm>> {
        let allPerms: BTreeMap<AppliedId, Vec<ProvenPerm>> = appIds
            .iter()
            .map(|x| ((*x).clone(), self.classes[&x.id].group().all_perms()))
            .collect();

        if CHECKS {
            self.checkPermsWithAppIds(appIds, &allPerms);
        }
        allPerms
    }

    fn createSlotsToNewIdx(&self, slotsToV: &BTreeMap<Slot, usize>, lab: &Vec<i32>) -> SlotMap {
        let mut vToSlots = BTreeMap::new();
        for (s, v) in slotsToV.iter() {
            let old = vToSlots.insert(*v, s.clone());
            assert!(old.is_none());
        }

        let mut slotsToNewIdx: SlotMap = SlotMap::new();
        // slot order is last
        for i in lab[(lab.len() - slotsToV.len())..].iter() {
            // first one is mapped to 0, 1, ...
            slotsToNewIdx.insert(
                vToSlots[&(*i as usize)],
                Slot::numeric(slotsToNewIdx.len() as u32),
            )
        }

        slotsToNewIdx
    }

    fn updateAppIds(
        &self,
        appIdsMut: &mut Vec<&mut AppliedId>,
        sortedAppIds: &Vec<AppliedId>,
        slotsToNewIdx: &SlotMap,
        allPerms: &BTreeMap<AppliedId, Vec<ProvenPerm>>,
    ) {
        assert_eq!(
            appIdsMut.len(),
            sortedAppIds.len(),
            "appIdsMut {appIdsMut:?}, sortedAppIds {sortedAppIds:?}"
        );
        for i in 0..appIdsMut.len() {
            *appIdsMut[i] = {
                let appId = &sortedAppIds[i];
                let perms: &Vec<_> = &allPerms[appId];
                if CHECKS {
                    assert!(
                        slotsToNewIdx.keys_set().is_superset(&appId.m.values_set()),
                        "appIdsMut {appIdsMut:?}, 
                        allPerms {allPerms:?},
                        i {i},
                    slotsToNewIdx {slotsToNewIdx:?}, 
                    appId {appId:?}"
                    );
                }

                // find min overall permutation
                perms
                    .into_iter()
                    .map(|p| AppliedId {
                        id: appId.id,
                        m: p.elem
                            .composePartial(&appId.m)
                            .compose_intersect(&slotsToNewIdx),
                    })
                    .min()
                    .unwrap()
            }
        }
    }

    // before
    // #[cfg(feature = "newShape")]
    // pub fn shapeMut(&self, eOrig: &mut L) -> Bijection {
    //     if eOrig.hasBind() {
    //         let ret = self.orig_shape(&eOrig);
    //         *eOrig = ret.0;
    //         return ret.1;
    //     }

    //     // weak shape domain to original domain
    //     self.find_enodeMut(eOrig);

    //     let origBij = eOrig.weak_shapeMut();

    //     let mut appIds: Vec<&AppliedId> = eOrig.applied_id_occurrences();

    //     if appIds.len() == 0 {
    //         return origBij;
    //     }

    //     // TODO: should we cache this?
    //     let allPerms: Vec<Vec<ProvenPerm>> = self.getAppIdsPerm(&appIds);
    //     let (lab, _, slotsToV) =
    //         canonAppIdsWithRename(&appIds, Some(&allPerms), self.canonAppIdsCache());

    //     let slotsToNewIdx = self.createSlotsToNewIdx(&slotsToV, &lab);

    //     let mut appIdsMut = eOrig.applied_id_occurrences_mut();
    //     // find smallest according to canonical label
    //     self.updateAppIds(&mut appIdsMut, &slotsToNewIdx, &allPerms);

    //     let bij = eOrig.weak_shapeMut();
    //     let res = slotsToNewIdx.composePartial(&bij.inverse()).inverse();
    //     res.compose(&origBij)
    // }

    // return (pos, len)
    fn findOrderVecPos(&self, enode: &L) -> Vec<(usize, usize)> {
        let mut orderVecPos = vec![];
        let childrenTypes = enode.getChildrenType();
        let mut counter = 0;
        for childType in childrenTypes {
            match childType {
                LanguageChildrenType::Vec(v) => {
                    counter += v.len();
                }
                LanguageChildrenType::OrderVec(v) => {
                    orderVecPos.push((counter, v.len()));
                    counter += v.len();
                }
                LanguageChildrenType::AppliedId => {
                    counter += 1;
                }
                _ => {
                    continue;
                }
            }
        }

        orderVecPos
    }

    fn sortAppIdsAtOrderVecPos(
        &self,
        appIds: &mut Vec<&AppliedId>,
        orderVecPos: &Vec<(usize, usize)>,
    ) {
        for (start, len) in orderVecPos {
            if *len <= 1 {
                continue;
            }
            let end = start + len;
            assert!(end <= appIds.len());
            appIds[*start..end].sort();
        }
    }

    fn checkOrderVecSplitIds(&self, appIds: &Vec<&AppliedId>, orderVecPos: &Vec<(usize, usize)>) {
        let mut idsNotIn = BTreeSet::new();
        let mut idsIn = BTreeSet::new();
        let mut rangeIdx = 0;

        for (idx, appId) in appIds.iter().enumerate() {
            while rangeIdx < orderVecPos.len()
                && idx >= orderVecPos[rangeIdx].0 + orderVecPos[rangeIdx].1
            {
                rangeIdx += 1;
            }

            let inOrderVec = if rangeIdx < orderVecPos.len() {
                let (start, len) = orderVecPos[rangeIdx];
                idx >= start && idx < start + len
            } else {
                false
            };

            if !inOrderVec {
                idsNotIn.insert(appId.id);
            } else {
                idsIn.insert(appId.id);
            }
        }

        // check they do not have overlap
        assert!(idsNotIn.is_disjoint(&idsIn));
    }

    fn reorderAppIds(
        &self,
        appIds: &Vec<&AppliedId>,
        appIdToV: &Vec<(AppliedId, usize)>,
        lab: &Vec<i32>,
    ) -> Vec<AppliedId> {
        assert_eq!(appIds.len(), appIdToV.len());
        let mut VToAppIds = BTreeMap::new();
        for (id, v) in appIdToV {
            let old = VToAppIds.insert(v, id);
            assert!(old.is_none());
        }

        if CHECKS {
            assert_eq!(
                appIdToV
                    .iter()
                    .map(|(a, _)| a.clone())
                    .collect::<BTreeSet<_>>(),
                appIds.iter().map(|a| (*a).clone()).collect::<BTreeSet<_>>()
            );
        }

        let mut sortedAppIds = vec![];
        // push in label order
        for i in &lab[0..appIds.len()] {
            sortedAppIds.push(VToAppIds[&(*i as usize)].clone());
        }

        sortedAppIds
    }

    fn checkIdsNotInOrderVecUnchanged(
        &self,
        appIdsOrig: &Vec<AppliedId>,
        appIdsMut: &Vec<&mut AppliedId>,
        orderVecPos: &Vec<(usize, usize)>,
    ) {
        assert_eq!(appIdsOrig.len(), appIdsMut.len());

        let mut rangeIdx = 0;
        for idx in 0..appIdsOrig.len() {
            while rangeIdx < orderVecPos.len()
                && idx >= orderVecPos[rangeIdx].0 + orderVecPos[rangeIdx].1
            {
                rangeIdx += 1;
            }

            let inOrderVec = if rangeIdx < orderVecPos.len() {
                let (start, len) = orderVecPos[rangeIdx];
                idx >= start && idx < start + len
            } else {
                false
            };

            if !inOrderVec {
                assert_eq!(
                    appIdsOrig[idx].id, appIdsMut[idx].id,
                    "non-OrderVec appId changed at index {idx}: orig {:?}, new {:?}",
                    appIdsOrig[idx], appIdsMut[idx]
                );
            }
        }
    }

    // with sort
    #[cfg(feature = "newShape")]
    pub fn shapeMut(&self, eOrig: &mut L) -> Bijection {
        if eOrig.hasBind() {
            let ret = self.orig_shape(&eOrig);
            *eOrig = ret.0;
            return ret.1;
        }

        // weak shape domain to original domain
        self.find_enodeMut(eOrig);

        let origBij = eOrig.weak_shapeMut();

        let mut appIds: Vec<&AppliedId> = eOrig.applied_id_occurrences();
        if appIds.len() == 0 {
            return origBij;
        }

        let appIdsOrig: Vec<AppliedId> = appIds.iter().map(|app_id| (*app_id).clone()).collect();

        let orderVecPos = self.findOrderVecPos(eOrig);
        if CHECKS {
            self.checkOrderVecSplitIds(&appIds, &orderVecPos);
        }
        self.sortAppIdsAtOrderVecPos(&mut appIds, &orderVecPos);

        // TODO: should we cache this?
        let allPerms: BTreeMap<AppliedId, Vec<ProvenPerm>> = self.getAppIdsToPerm(&appIds);
        let (lab, appIdToV, slotsToV) = canonAppIdsWithRename(
            &appIds,
            Some(&allPerms),
            Some(&orderVecPos),
            self.canonAppIdsCache(),
        );

        let slotsToNewIdx = self.createSlotsToNewIdx(&slotsToV, &lab);
        // println!("appIds {appIds:?}");
        // println!("appIdToV {appIdToV:?}");
        // TODO: reorder must check orderVec first
        let sortedAppIds = self.reorderAppIds(&appIds, &appIdToV, &lab);
        let mut appIdsMut = eOrig.applied_id_occurrences_mut();
        // find smallest according to canonical label
        self.updateAppIds(&mut appIdsMut, &sortedAppIds, &slotsToNewIdx, &allPerms);
        if CHECKS {
            self.checkIdsNotInOrderVecUnchanged(&appIdsOrig, &appIdsMut, &orderVecPos);
        }

        let bij = eOrig.weak_shapeMut();
        let res = slotsToNewIdx.composePartial(&bij.inverse()).inverse();
        res.compose(&origBij)
    }

    #[allow(unused)]
    pub(crate) fn proven_shape(&self, e: &L) -> (ProvenNode<L>, Bijection) {
        self.proven_proven_shape(&self.refl_pn(e))
    }

    #[allow(unused)]
    pub(crate) fn proven_proven_shape(&self, e: &ProvenNode<L>) -> (ProvenNode<L>, Bijection) {
        let tmp = self.proven_proven_pre_shape(&e);
        let tmpWS = tmp.orig_weak_shape();
        tmpWS
    }

    // get the smallest weak shape, where different shapes are from permutation of children eclasses
    #[allow(unused)]
    pub(crate) fn proven_proven_pre_shape(&self, e: &ProvenNode<L>) -> ProvenNode<L> {
        trace!("doing proven_proven_pre_shape on {:?}", e.elem);
        // TODO: I want to print enode that takes a long time on shape as an expression
        // But this will also call shape
        // if DETAILS {
        //     let map = &mut BTreeMap::<AppliedId, RecExpr<L>>::new();
        //     let expr = self.getENodeExprRecur(&e.elem, map);
        //     trace!("enode expr: {expr:?}");
        // }
        let e = self.proven_proven_find_enode(e);
        let ret = self
            .proven_proven_get_group_compatible_variants(&e)
            .into_iter()
            .min_by_key(|pn| pn.weak_shape().0.elem.all_slot_occurrences())
            .unwrap();
        trace!(
            "done proven_proven_pre_shape -> {ret:?}
        {:?}",
            ret.elem.orig_weak_shape()
        );
        ret
    }

    // We want to compute the shape of an e-node n := f(c[$x, $y], c[$y, $x]), where c[$x, $y] = c[$y, $x].
    // The (strong) shape of f(c[$x, $y], c[$y, $x]) is f(c[$0, $1], c[$0, $1]), whereas the
    //     weak     shape of f(...)                  is f(c[$0, $1], c[$1, $0]).
    // Basically, the weak shape doesn't respect group symmetries, while the strong shape does.

    // We first compute the set of e-nodes equivalent to n by group symmetries.
    // This set would be
    // {f(c[$x, $y], c[$y, $x]),
    //  f(c[$y, $x], c[$y, $x]),
    //  f(c[$x, $y], c[$x, $y]),
    //  f(c[$y, $x], c[$x, $y])}
    // This set is what the proven_proven_get_group_compatible_variants returns.
    // Now: we want to compute the "weak shapes" of them, which means to replace names by numbers (by going through the slots left to right).
    // When computing the weak shapes, we only have
    // {f(c[$0, $1], c[$1, $0]),
    //  f(c[$0, $1], c[$0, $1])}
    // This is what get_group_compatible_weak_variants would return.
    pub(crate) fn proven_proven_get_group_compatible_variants(
        &self,
        enode: &ProvenNode<L>,
    ) -> Vec<ProvenNode<L>> {
        // #[cfg(feature = "newSymCal")]
        // panic!("should not be called");

        trace!("doing proven_proven_get_group_compatible_variants");
        // should only be called with an up-to-date e-node.
        if CHECKS {
            for x in enode.elem.applied_id_occurrences() {
                assert!(self.is_alive(x.id));
            }
        }

        let mut out = Vec::new();

        // early-return, if groups are all trivial.
        if enode
            .elem
            .ids()
            .iter()
            .all(|i| self.classes[i].group().is_trivial())
        {
            out.push(enode.clone());
            return out;
        }

        // permutation information is generated from children eclasses
        let groups: Vec<Vec<ProvenPerm>> = enode
            .elem
            .applied_id_occurrences()
            .iter()
            .map(|x| {
                self.classes[&x.id]
                    .group()
                    .all_perms()
                    .into_iter()
                    .collect()
            })
            .collect();

        trace!("cartesian: ");
        for g in groups.iter() {
            trace!("{} ", g.len());
        }
        trace!("allPerms {:?}", groups);
        for perms in &groups {
            if perms.len() > 1 {
                for perm in perms.iter() {
                    let perm = &perm.elem;
                    let mut s: String = "".to_string();
                    for (from, to) in perm.iter() {
                        if from != to {
                            s += &format!("{:?} -> {:?} ", from, to);
                        }
                    }
                    if s.len() > 0 {
                        trace!("{s}");
                    }
                }
            }
        }
        trace!(
            "\n = {}\n",
            groups.iter().map(|x| x.len()).product::<usize>()
        );

        for l in cartesian(&groups) {
            let pn = enode.clone();

            let pn = self.chain_pn_map(&pn, |i, pai| self.chain_pai_pp(&pai, l[i]));

            // TODO fix check.
            // if CHECKS { pn.check_base(enode.base()); }
            out.push(pn);
        }

        trace!("done proven_proven_get_group_compatible_variants");
        out
    }

    // for all AppliedIds that are contained in `enode`, permute their arguments as their groups allow.
    // TODO every usage of this function hurts performance drastically. Which of them can I eliminate?
    pub(crate) fn proven_get_group_compatible_variants(&self, enode: &L) -> Vec<ProvenNode<L>> {
        self.proven_proven_get_group_compatible_variants(&self.refl_pn(enode))
    }

    pub(crate) fn get_group_compatible_variants(&self, enode: &L) -> Vec<L> {
        self.proven_get_group_compatible_variants(enode)
            .into_iter()
            .map(|pnode| pnode.elem)
            .collect()
    }

    pub fn get_group_compatible_weak_variants(&self, enode: &L) -> Vec<L> {
        // println!("get_group_compatible_weak_variants {enode:?}");
        let set = self.get_group_compatible_variants(enode);
        let mut shapes = SmallHashSet::empty();
        let mut out = Vec::new();

        for x in set {
            let (sh, _) = x.weak_shape();
            if shapes.contains(&sh) {
                continue;
            }
            shapes.insert(sh);
            out.push(x);
        }

        // println!("{out:?}");

        out
    }
}
