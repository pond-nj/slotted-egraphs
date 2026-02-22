use crate::*;
use log::{debug, info, trace};

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    // proof.l should be i.
    // proof.r should be missing a few slots.
    fn record_redundancy_witness(
        &mut self,
        i: Id,
        cap: &SmallHashSet<Slot>,
        #[allow(unused)] proof: ProvenEq,
    ) {
        debug!("start record_redundancy_witness");
        if CHECKS {
            assert!(self.is_alive(i));

            #[cfg(feature = "explanations")]
            assert_eq!(proof.l.id, i);
        }

        #[cfg(feature = "explanations")]
        let prf = {
            let flipped = prove_symmetry(proof.clone(), &self.proof_registry);
            let new_prf = prove_transitivity(proof, flipped, &self.proof_registry);

            let old_prf = self
                .proven_find_applied_id(&self.mk_syn_identity_applied_id(i))
                .proof;
            prove_transitivity(new_prf, old_prf, &self.proof_registry)
        };

        let elem = self
            .mk_syn_identity_applied_id(i)
            .apply_slotmap_intersect(&SlotMap::identity(cap));

        #[cfg(feature = "explanations")]
        if CHECKS {
            let eq = prf.equ();
            let elem2 = eq.r.apply_slotmap_intersect(&eq.l.m.inverse());
            assert_eq!(elem, elem2);
        }

        trace!("call unionfind_set from record_redundancy_witness");
        self.unionfind_set(
            i,
            ProvenAppliedId {
                elem,

                #[cfg(feature = "explanations")]
                proof: prf,
            },
        );
        debug!("done record_redundancy_witness");
    }

    // We expect `from` to be on the lhs of this equation.
    pub fn shrink_slots(&mut self, from: &AppliedId, cap: &SmallHashSet<Slot>, proof: ProvenEq) {
        #[cfg(feature = "explanations")]
        if CHECKS {
            assert_eq!(from.id, proof.l.id);
        }
        if CHECKS {
            assert!(self.is_alive(from.id));
        }

        // stuff that sends to cap from 'from'
        let origcap = cap.iter().map(|x| from.m.inverse()[*x]).collect();
        self.record_redundancy_witness(from.id, &origcap, proof);

        let (id, cap) = {
            // from.m :: slots(from.id) -> X
            // cap :: set X

            // m_inv :: X -> slots(from.id)
            let m_inv = from.m.inverse();

            // cap :: set slots(from.id)
            let new_cap: SmallHashSet<Slot> = cap.iter().map(|x| m_inv[*x]).collect();

            if CHECKS {
                assert!(new_cap == origcap);
            }

            (from.id, new_cap)
        };

        // cap :: set slots(id)

        let syn_slots = &self.syn_slots(id);
        let c = self.classes.get_mut(&id).unwrap();
        let grp = &c.group();

        let mut final_cap = cap.clone();

        // d is a newly redundant slot.
        for d in &c.slots - &cap {
            // if d is redundant, then also the orbit of d is redundant.
            final_cap = &final_cap - &grp.orbit(d);
        }

        // update class slots
        c.slots = cap.clone();
        let oldGenerators = c.group().generators();
        let _ = c;

        let restrict_proven = |proven_perm: ProvenPerm| {
            if CHECKS {
                proven_perm.check();
            }

            // only keep the map from an element in cap
            let perm: SlotMap = proven_perm
                .elem
                .into_iter()
                .filter(|(x, _)| cap.contains(x))
                .collect();

            assert!(perm.len() != 0);

            #[cfg(feature = "explanations")]
            let prf = self.disassociate_proven_eq(proven_perm.proof);
            let out = ProvenPerm {
                elem: perm,
                #[cfg(feature = "explanations")]
                proof: prf,
                #[cfg(feature = "explanations")]
                reg: self.proof_registry.clone(),
            };
            if CHECKS {
                out.check();
            }
            out
        };

        let generators = oldGenerators.into_iter().map(restrict_proven).collect();
        let identity = ProvenPerm::identity(id, &cap, syn_slots, self.proof_registry.clone());
        if CHECKS {
            identity.check();
        }
        let c = self.classes.get_mut(&id).unwrap();
        *c.groupMut() = Group::new(&identity, generators);

        self.touched_class(from.id, PendingType::Full);
    }

    pub fn rebuild(&mut self) {
        println!("start rebuild");
        if CHECKS {
            self.check();
        }

        trace!("start pending loops");
        while !self.pending.is_empty() {
            let pending_batch = std::mem::take(&mut self.pending);
            for (sh, pending_ty) in pending_batch {
                trace!("deal with pending {sh:?}");
                self.handleSorted(&sh);
                self.handle_pending(&sh, pending_ty);
            }

            // expensive invariants check: run once per batch instead of once per item
            if CHECKS {
                self.check();
            }
        }
        info!("end pending loops");

        info!("start modify_queue");
        while let Some(i) = self.modify_queue.pop() {
            let i = self.find_id(i);
            N::modify(self, i);
        }
        info!("end modify_queue");
        println!("done rebuild");
    }

    pub fn handleSorted(&mut self, sh: &L) {
        debug!("start handleSorted");
        let lenBefore = self.total_number_of_nodes();
        if self.hashcons.get(&sh).is_none() {
            return;
        }

        let i = self.hashcons[&sh];

        let enode = &sh.apply_slotmap(&self.classes[&i].nodes[&sh].elem);
        // let enodeBeforeFind = enode;
        let enode = self.find_enode(enode);
        // TODO: this should be blocked in the future
        // if enode == *enodeBeforeFind {
        //     return;
        // }
        let app_i = self.mk_sem_identity_applied_id(i);
        assert_eq!(app_i, self.find_applied_id(&app_i));

        let sortedENode = enode.sorted();
        let lookupSortedRes = self.lookup_internal(&self.shape(&sortedENode));
        if lookupSortedRes.is_some() && lookupSortedRes.unwrap() != app_i {
            // println!("eclass {:?}", self.eclass(app_i.id));
            // println!("enode before find {:?}", enodeBeforeFind);
            // println!("enode before sort {:?}", enode);
            // println!("enode after sort {:?}", sortedENode);
            // println!("app_i {:?}", app_i);
            let afterSortedAppId = self.add(sortedENode.clone());
            // assert_ne!(enode, *enodeBeforeFind);
            self.union_justified(
                &app_i,
                &afterSortedAppId,
                Some("Union Sorted ENode, Rebuild".to_string()),
            );
        }
        assert!(self.total_number_of_nodes() == lenBefore);
        debug!("end handleSorted");
    }

    fn handle_pending(&mut self, sh: &L, _pending_ty: PendingType) {
        // TODO: this is a hack to make the test pass
        debug!("start handle_pending");
        trace!("handle_pending {sh:?}");
        if self.hashcons.get(&sh).is_none() {
            return;
        }
        let i = self.hashcons[&sh];

        /*
        let t = self.shape(&sh);
        if t.0 != sh {
            let psn = self.raw_remove_from_class(i, sh.clone());
            self.raw_add_to_class(i.id, (t.clone(), todo!());
        }
        */

        // (Pond) update analysis first but then might remove this node later?????, why???
        // debug!("Eclass {:?}", self.eclass(i).unwrap());
        // self.update_analysis(&sh, i);

        // if let PendingType::OnlyAnalysis = pending_ty {
        //     debug!("end handling pending at OnlyAnalysis");
        //     return;
        // }

        let psn = self.classes[&i].nodes[&sh].clone();
        let enode = &sh.apply_slotmap(&psn.elem);
        self.raw_remove_from_class(i, sh.clone());
        let app_i = self.mk_sem_identity_applied_id(i);

        let src_id = psn.src_id;

        let mut enode = self.find_enode(&enode);
        let mut i = self.find_applied_id(&app_i);
        assert_eq!(i, app_i);
        // i.m :: slots(i) -> X
        // i_orig.m :: slots(i_orig) -> X
        if !i.slots().is_subset(&enode.slots()) {
            self.handle_shrink_in_upwards_merge(src_id);

            enode = self.find_enode(&enode);
            i = self.find_applied_id(&i);
        }

        let t = self.shape(&enode);

        // upwards merging found a match!
        // if there's another Enode in Egraph already
        let lookupRes = self.lookup_internal(&t);
        if lookupRes.is_some() {
            self.handle_congruence(self.pc_from_src_id(src_id));
            debug!("end handle_pending by congruence");
            return;
        }

        let (sh, bij) = t;
        let mut m = i.m.inverse();

        for x in bij.values_set() {
            if !m.contains_key(x) {
                m.insert(x, Slot::fresh());
            }
        }
        trace!("app_i {app_i:?}");
        trace!("bij {bij:?}");
        trace!("m {m:?}");
        let bij = bij.compose(&m);
        let t = (sh.clone(), bij.clone());
        self.raw_add_to_class(i.id, t.clone(), src_id);

        self.update_analysis(&sh, app_i.id);

        self.determine_self_symmetries(src_id);
        debug!("end handle_pending");
    }

    fn update_analysis(&mut self, sh: &L, i: Id) {
        // call make on this Enode
        trace!("sh {sh:?}");
        let v = N::make(self, sh);
        trace!("sh data {v:#?}");
        trace!("i eclass {:?} {:?}", i, self.eclass(i).unwrap());

        // let c = self.classes.get_mut(&i).unwrap();
        // let old = c.analysis_data.clone();
        let oldData = self.analysis_data(i).clone();
        // merge with old data
        trace!("merge call from update_analysis");
        let new = N::merge(oldData.clone(), v, i, None, self);
        let updateData = self.analysis_data_mut(i);
        // c.analysis_data = new.clone();
        let changed = new != oldData;
        *updateData = new;

        if changed {
            self.modify_queue.push(i);
            self.touched_class(i, PendingType::OnlyAnalysis);
        }
    }

    fn handle_shrink_in_upwards_merge(&mut self, src_id: Id) {
        let pc1 = self.pc_from_src_id(src_id);
        let pc2 = self.chain_pc_map(&pc1, |_, pai| self.proven_proven_find_applied_id(&pai));

        let (a, b, prf) = self.pc_congruence(&pc1, &pc2);

        let cap = &a.slots() & &b.slots();

        self.shrink_slots(&a, &cap, prf);
    }

    pub(in crate::egraph) fn handle_congruence(&mut self, pc1: ProvenContains<L>) {
        let (sh, _) = self.shape(&pc1.node.elem);
        let pc2 = self.pc_from_shape(&sh);

        let (a, b, prf) = self.pc_congruence(&pc1, &pc2);

        self.union_internal(&a, &b, prf);
    }

    // add parent to pending
    // upon touching an e-class, you need to update all usages of it.
    pub(crate) fn touched_class(&mut self, i: Id, pending_ty: PendingType) {
        for sh in self.classes[&i].usages() {
            let v = self.pending.entry(sh.clone()).or_insert(pending_ty);
            *v = v.merge(pending_ty);
        }
    }

    pub(crate) fn pc_from_shape(&self, sh: &L) -> ProvenContains<L> {
        let i = self
            .hashcons
            .get(&sh)
            .expect("pc_from_shape should only be called if the shape exists in the e-graph!");
        let c = self.classes[&i].nodes[&sh].src_id;

        // this shall change! Later on we want to deprecate the src-id.
        self.pc_from_src_id(c)
    }
}
