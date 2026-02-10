use super::*;

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
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

    #[cfg(feature = "newShape")]
    pub fn shape(&self, eOrig: &L) -> (L, Bijection) {
        trace!("call shape {eOrig:?}");
        let e = self.find_enode(eOrig);

        let childrenType = e.getChildrenType();
        if childrenType.contains(&LanguageChildrenType::Bind) {
            trace!("ret shape {eOrig:?}");
            return self.orig_shape(eOrig);
        }

        let appIds: Vec<AppliedId> = e
            .applied_id_occurrences()
            .into_iter()
            .map(|x| (*x).clone())
            .collect();

        if appIds.len() == 0 {
            trace!(
                "shape {eOrig:?} -> {:?} {:?}",
                e.orig_weak_shape().0,
                e.orig_weak_shape().1
            );
            trace!("ret shape {eOrig:?}");
            return e.orig_weak_shape();
        }
        let allPerms: Vec<Vec<ProvenPerm>> = appIds
            .iter()
            .map(|x| {
                self.classes[&x.id]
                    .group()
                    .all_perms()
                    .into_iter()
                    .collect()
            })
            .collect();
        let (lab, _, slotsToV) = canonicalLabelAppIds(&appIds, Some(&allPerms));

        trace!(
            "allPerms {:?}\n orig_weak_shape {:?}",
            allPerms,
            eOrig.orig_weak_shape()
        );

        let mut vToSlots = BTreeMap::new();
        for (s, v) in slotsToV.iter() {
            assert!(vToSlots.insert(*v, s.clone()).is_none());
        }

        let mut slotsToNewIdx: SlotMap = SlotMap::new();
        for i in lab[(lab.len() - slotsToV.len())..].iter() {
            slotsToNewIdx.insert(
                vToSlots[&(*i as usize)],
                Slot::numeric(slotsToNewIdx.len() as u32),
            )
        }

        let mut shaped: Vec<AppliedId> = vec![];
        for appId in appIds {
            let perms: Vec<_> = self.classes[&appId.id]
                .group()
                .all_perms()
                .into_iter()
                .collect();
            trace!("id {} allPerms {:?}", appId.id, perms);
            trace!("appId.m {:?}", appId.m);
            if CHECKS {
                assert!(slotsToNewIdx.keys_set().is_superset(&appId.m.values_set()));
            }

            shaped.push(
                perms
                    .into_iter()
                    .map(|p| AppliedId {
                        id: appId.id,
                        m: p.elem
                            .composePartial(&appId.m)
                            .compose_intersect(&slotsToNewIdx),
                    })
                    .min()
                    .unwrap(),
            );
        }

        let mut eNew = e.clone();
        let mut appIdsMut = eNew.applied_id_occurrences_mut();
        let n = appIdsMut.len();
        for i in 0..n {
            *appIdsMut[i] = shaped[i].clone();
        }

        // find smallest according to canonical label

        trace!(
            "shape result {eOrig:?} -> {:?} {:?}",
            eNew,
            slotsToNewIdx.inverse()
        );
        trace!("orig_weak_shape {:?}", eOrig.orig_weak_shape());
        trace!("eOrig {eOrig:?}");
        trace!("eOrig orig_weak_shape {:?}", eOrig.orig_weak_shape());
        trace!("eNew {eNew:?}");
        let (eNewWS, bij) = eNew.orig_weak_shape();
        trace!("slotsToNewIdx {slotsToNewIdx:?}");
        trace!("eNewWS {eNewWS:?}");
        trace!("bij {bij:?}");
        let res = slotsToNewIdx.composePartial(&bij.inverse()).inverse();
        trace!("res {res:?}");
        trace!("ret shape {eOrig:?}");
        (eNewWS, res)
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
        // println!("doing proven_proven_get_group_compatible_variants");
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
        trace!(
            "\n = {}\n",
            groups.iter().map(|x| x.len()).product::<usize>()
        );

        // println!("doing cartesian on groups {groups:?}");
        for l in cartesian(&groups) {
            // println!("l {l:?}");
            let pn = enode.clone();
            // println!("pn before {pn:?}");
            let pn = self.chain_pn_map(&pn, |i, pai| self.chain_pai_pp(&pai, l[i]));
            // println!("pn after {pn:?}");
            // TODO fix check.
            // if CHECKS { pn.check_base(enode.base()); }
            out.push(pn);
        }

        // println!("done proven_proven_get_group_compatible_variants");
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

        out
    }
}
