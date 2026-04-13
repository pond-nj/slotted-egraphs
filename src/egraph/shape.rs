use std::cell::{Ref, RefMut};

use log::info;

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

    fn checkPermsWithAppIds(&self, appIds: &Vec<&AppliedId>, allPerms: &Vec<Vec<ProvenPerm>>) {
        for (i, perms) in allPerms.iter().enumerate() {
            let appId = &appIds[i];
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

    fn getAppIdsPerm(&self, appIds: &Vec<&AppliedId>) -> Vec<Vec<ProvenPerm>> {
        let allPerms = appIds
            .iter()
            .map(|x| self.classes[&x.id].group().all_perms())
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
        for i in lab[(lab.len() - slotsToV.len())..].iter() {
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
        slotsToNewIdx: &SlotMap,
        allPerms: &Vec<Vec<ProvenPerm>>,
    ) {
        for i in 0..appIdsMut.len() {
            *appIdsMut[i] = {
                let appId = &appIdsMut[i];
                let perms: &Vec<_> = &allPerms[i];
                if CHECKS {
                    assert!(slotsToNewIdx.keys_set().is_superset(&appId.m.values_set()));
                }

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

    #[cfg(feature = "newShape")]
    // TODO: it seems for some reason this function changes depends on the input slots
    // like even if the weak shape is the same, it can output two different stuffs
    pub fn shape(&self, eOrig: &L) -> (L, Bijection) {
        if eOrig.hasBind() {
            let ret = self.orig_shape(&eOrig);
            return ret;
        }

        let mut eOrig = eOrig.clone();
        let origBij = eOrig.weak_shapeMut();

        self.find_enodeMut(&mut eOrig);
        let mut enodeAfterFind = eOrig;

        let appIds: Vec<&AppliedId> = enodeAfterFind.applied_id_occurrences();

        if appIds.len() == 0 {
            let bij = enodeAfterFind.weak_shapeMut();
            return (enodeAfterFind, bij.compose(&origBij));
        }

        // TODO: should we cache this?
        let allPerms: Vec<Vec<ProvenPerm>> = self.getAppIdsPerm(&appIds);
        let (lab, _, slotsToV) =
            canonAppIdsWithRename(&appIds, Some(&allPerms), self.canonAppIdsCache());

        let slotsToNewIdx = self.createSlotsToNewIdx(&slotsToV, &lab);
        // let shaped = self.createUpdatedAppIds(&appIds, &slotsToNewIdx, &allPerms);

        let mut appIdsMut = enodeAfterFind.applied_id_occurrences_mut();
        self.updateAppIds(&mut appIdsMut, &slotsToNewIdx, &allPerms);

        // find smallest according to canonical label

        let (eNewWS, bij) = enodeAfterFind.orig_weak_shape();
        let res = slotsToNewIdx.composePartial(&bij.inverse()).inverse();
        let ret = (eNewWS, res.compose(&origBij));
        ret
    }

    // TODO: we want to change everything to mutable version
    pub fn shapeMut(&self, eOrig: &mut L) -> Bijection {
        if eOrig.hasBind() {
            let ret = self.orig_shape(&eOrig);
            *eOrig = ret.0;
            return ret.1;
        }

        let origBij = eOrig.weak_shapeMut();

        self.find_enodeMut(eOrig);

        let appIds: Vec<&AppliedId> = eOrig.applied_id_occurrences();

        if appIds.len() == 0 {
            return eOrig.weak_shapeMut().compose(&origBij);
        }

        // TODO: should we cache this?
        let allPerms: Vec<Vec<ProvenPerm>> = self.getAppIdsPerm(&appIds);
        let (lab, _, slotsToV) =
            canonAppIdsWithRename(&appIds, Some(&allPerms), self.canonAppIdsCache());

        let slotsToNewIdx = self.createSlotsToNewIdx(&slotsToV, &lab);
        // let shaped = self.createUpdatedAppIds(&appIds, &slotsToNewIdx, &allPerms);

        let mut appIdsMut = eOrig.applied_id_occurrences_mut();
        self.updateAppIds(&mut appIdsMut, &slotsToNewIdx, &allPerms);

        // find smallest according to canonical label

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
