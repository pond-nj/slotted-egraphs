use crate::*;
use log::debug;

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    // proof.l should be i.
    // proof.r should be missing a few slots.
    fn record_redundancy_witness(
        &mut self,
        i: Id,
        cap: &SmallHashSet<Slot>,
        #[allow(unused)] proof: ProvenEq,
    ) {
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
            .apply_slotmap_partial(&SlotMap::identity(cap));

        #[cfg(feature = "explanations")]
        if CHECKS {
            let eq = prf.equ();
            let elem2 = eq.r.apply_slotmap_partial(&eq.l.m.inverse());
            assert_eq!(elem, elem2);
        }

        self.unionfind_set(
            i,
            ProvenAppliedId {
                elem,

                #[cfg(feature = "explanations")]
                proof: prf,
            },
        );
    }

    // We expect `from` to be on the lhs of this equation.
    pub(crate) fn shrink_slots(
        &mut self,
        from: &AppliedId,
        cap: &SmallHashSet<Slot>,
        proof: ProvenEq,
    ) {
        #[cfg(feature = "explanations")]
        if CHECKS {
            assert_eq!(from.id, proof.l.id);
        }

        debug!("Call shrink slots");
        debug!("from {:?}", from);
        debug!("cap {:?}", cap);
        let origcap = cap.iter().map(|x| from.m.inverse()[*x]).collect();
        debug!("origcap {:?}", origcap);
        self.record_redundancy_witness(from.id, &origcap, proof);

        let (id, cap) = {
            // from.m :: slots(from.id) -> X
            // cap :: set X

            // m_inv :: X -> slots(from.id)
            let m_inv = from.m.inverse();

            // cap :: set slots(from.id)
            let new_cap: SmallHashSet<Slot> = cap.iter().map(|x| m_inv[*x]).collect();

            // Pond:
            assert!(new_cap == origcap);

            (from.id, new_cap)
        };

        debug!("new cap {:?}", cap);

        // cap :: set slots(id)

        let syn_slots = &self.syn_slots(id);
        let c = self.classes.get_mut(&id).unwrap();
        let grp = &c.group;

        let mut final_cap = cap.clone();

        // d is a newly redundant slot.
        for d in &c.slots - &cap {
            // if d is redundant, then also the orbit of d is redundant.
            final_cap = &final_cap - &grp.orbit(d);
        }

        // update Eclass slots
        debug!("before change c.slots {c:?}");
        c.slots = cap.clone();
        debug!("after change c.slots {c:?}");
        let generators = c.group.generators();
        let _ = c;

        let restrict_proven = |proven_perm: ProvenPerm| {
            if CHECKS {
                proven_perm.check();
            }

            let perm = proven_perm
                .elem
                .into_iter()
                .filter(|(x, _)| cap.contains(x))
                .collect();

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

        let generators = generators.into_iter().map(restrict_proven).collect();
        let identity = ProvenPerm::identity(id, &cap, syn_slots, self.proof_registry.clone());
        if CHECKS {
            identity.check();
        }
        let c = self.classes.get_mut(&id).unwrap();
        c.group = Group::new(&identity, generators);

        self.touched_class(from.id, PendingType::Full);
    }

    pub(crate) fn rebuild(&mut self) {
        if CHECKS {
            self.check();
        }

        while let Some(sh) = self.pending.keys().cloned().next() {
            let pending_ty = self.pending.remove(&sh).unwrap();
            self.handle_pending(sh, pending_ty);

            if CHECKS {
                self.check();
            }
        }

        while let Some(i) = self.modify_queue.pop() {
            let i = self.find_id(i);
            N::modify(self, i);
        }
    }

    fn handle_pending(&mut self, sh: L, _pending_ty: PendingType) {
        let i = self.hashcons[&sh];
        debug!("begin of handle_pending {i:?}");
        debug!("{:?}", self.eclass(i).unwrap());

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
        let node = sh.apply_slotmap(&psn.elem);
        self.raw_remove_from_class(i, sh.clone());
        let app_i = self.mk_sem_identity_applied_id(i);

        let enode = &node;
        let i_orig = &app_i;
        let src_id = psn.src_id;

        let mut enode = self.find_enode(&enode);
        let mut i = self.find_applied_id(i_orig);
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
        if self.lookup_internal(&t).is_some() {
            self.handle_congruence(self.pc_from_src_id(src_id));
            debug!("end handling pending at 1");
            return;
        }

        let (sh, bij) = t;
        let mut m = i.m.inverse();

        for x in bij.values() {
            if !m.contains_key(x) {
                m.insert(x, Slot::fresh());
            }
        }
        let bij = bij.compose(&m);
        let t = (sh.clone(), bij);
        self.raw_add_to_class(i.id, t.clone(), src_id);

        debug!("Eclass {:?}", self.eclass(i_orig.id).unwrap());
        self.update_analysis(&sh, i_orig.id);

        self.determine_self_symmetries(src_id);

        debug!("end of handle_pending {i:?}");
        debug!("{:?}", self.eclass(i.id).unwrap());
    }

    fn update_analysis(&mut self, sh: &L, i: Id) {
        debug!("from update_analysis {i:?} {:?}", sh);
        debug!("{:?}", self.eclass(i).unwrap());

        // call make on this Enode
        let v = N::make(self, sh);

        // let c = self.classes.get_mut(&i).unwrap();
        // let old = c.analysis_data.clone();
        let oldData = self.analysis_data(i).clone();
        // merge with old data
        let new = N::merge(oldData.clone(), v, i, self);
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

    // finds self-symmetries caused by the e-node `src_id`.
    fn determine_self_symmetries(&mut self, src_id: Id) {
        let pc1 = self.pc_from_src_id(src_id);

        let i = pc1.target_id();
        let weak = pc1.node.elem.weak_shape().0;
        for pn2 in self.proven_proven_get_group_compatible_variants(&pc1.node) {
            let pc2 = ProvenContains {
                pai: pc1.pai.clone(),
                node: pn2,
            };
            let (weak2, _) = pc2.node.elem.weak_shape();
            if weak == weak2 {
                if CHECKS {
                    self.check_pc(&pc1);
                }
                if CHECKS {
                    self.check_pc(&pc2);
                }
                if CHECKS {
                    assert_eq!(pc1.target_id(), pc2.target_id());
                }

                #[allow(unused)]
                let (a, b, proof) = self.pc_congruence(&pc1, &pc2);

                // or is it the opposite direction? (flip a with b)
                let perm = a.m.compose(&b.m.inverse());

                let proven_perm = ProvenPerm {
                    elem: perm,

                    #[cfg(feature = "explanations")]
                    proof,

                    #[cfg(feature = "explanations")]
                    reg: self.proof_registry.clone(),
                };

                if CHECKS {
                    proven_perm.check();
                }
                let grp = &mut self.classes.get_mut(&i).unwrap().group;
                if grp.add(proven_perm) {
                    self.touched_class(i, PendingType::Full);
                }
            }
        }
    }

    pub(in crate::egraph) fn handle_congruence(&mut self, pc1: ProvenContains<L>) {
        let (sh, _) = self.shape(&pc1.node.elem);
        let pc2 = self.pc_from_shape(&sh);

        let (a, b, prf) = self.pc_congruence(&pc1, &pc2);
        if a.id != b.id {
            debug!("handle_congruence, union a {a:?}, b {b:?}");
        }
        self.union_internal(&a, &b, prf);
    }

    // add parent to pending
    // upon touching an e-class, you need to update all usages of it.
    pub(crate) fn touched_class(&mut self, i: Id, pending_ty: PendingType) {
        for sh in &self.classes[&i].usages {
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
