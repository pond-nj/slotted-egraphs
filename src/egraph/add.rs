use std::collections::{BTreeMap, BTreeSet};

use vec_collections::AbstractVecSet;

use crate::*;
use log::{debug, info, trace, warn};

// syntactic add:
impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    pub fn getENode(&self, enodeId: ENodeId) -> &L {
        let ret = &self.enodes[enodeId.0];
        if CHECKS {
            let weakShape = ret.weak_shape().0;
            assert_eq!(ret, &weakShape);
        }
        ret
    }

    pub fn getOrAddENodeId(&mut self, enode: &L) -> ENodeId {
        if CHECKS {
            let weakShape = enode.weak_shape().0;
            assert_eq!(enode, &weakShape);
        }

        if self.enodeWeakShape.contains_key(&enode.weak_shape().0) {
            return self.enodeWeakShape[&enode.weak_shape().0];
        }

        let id = self.enodes.len();
        self.enodeWeakShape
            .insert(enode.weak_shape().0, ENodeId(id));
        self.enodes.push(enode.clone());
        ENodeId(id)
    }

    pub(crate) fn getENodeId(&self, enode: &L) -> Option<ENodeId> {
        if CHECKS {
            let weakShape = enode.weak_shape().0;
            assert_eq!(enode, &weakShape);
        }
        self.enodeWeakShape.get(&enode.weak_shape().0).cloned()
    }

    pub fn add_syn_expr(&mut self, re: &RecExpr<L>) -> AppliedId {
        let mut n = re.node.clone();
        let mut refs: Vec<&mut AppliedId> = n.applied_id_occurrences_mut();
        if CHECKS {
            assert_eq!(re.children.len(), refs.len());
        }
        for (i, child) in re.children.iter().enumerate() {
            *(refs[i]) = self.add_syn_expr(&child);
        }
        let ret = self.add_syn(&n);
        debug!("add_syn_expr: {} <-> {}", ret, re);
        ret
    }

    pub fn add_syn(&mut self, enode: &L) -> AppliedId {
        #[cfg(not(feature = "explanations"))]
        {
            self.add(enode)
        }

        #[cfg(feature = "explanations")]
        {
            let enode = self.synify_enode(enode);

            self.add(enode.clone());

            if let Some(x) = self.lookup_syn(&enode) {
                if CHECKS {
                    assert_eq!(enode.slots(), x.slots());
                }
                return x;
            }

            let old_slots = enode.slots();
            let fresh_to_old = Bijection::bijection_from_fresh_to(&old_slots);
            let old_to_fresh = fresh_to_old.inverse();
            let new_enode = enode.apply_slotmap(&old_to_fresh);
            let c = self.alloc_eclass(&old_to_fresh.values(), new_enode.clone());

            let pc = self.pc_find(&self.refl_pc(c));

            self.handle_congruence(pc);

            let c_a = self.mk_syn_applied_id(c, fresh_to_old.clone());
            if CHECKS {
                assert_eq!(enode.slots(), c_a.slots());
            }

            c_a
        }
    }

    #[cfg(feature = "explanations")]
    fn lookup_syn(&self, enode: &L) -> Option<AppliedId> {
        let (sh, bij) = enode.weak_shape();
        let i = self.syn_hashcons.get(&sh)?;

        // bij :: SHAPE -> X
        // i :: slots(i.id) -> SHAPE
        let i = i.apply_slotmap(&bij);
        Some(i)
    }
}

// semantic add:
impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    pub fn addExprGetENode(&mut self, re: &str) -> (AppliedId, L) {
        let re = RecExpr::parse(re).unwrap();

        let mut n: L = re.node;
        let mut refs: Vec<&mut AppliedId> = n.applied_id_occurrences_mut();
        if CHECKS {
            assert_eq!(re.children.len(), refs.len());
        }
        // recursively add children
        for (i, child) in re.children.into_iter().enumerate() {
            *(refs[i]) = self.add_expr(child);
        }
        (self.add(&n), n)
    }

    pub fn addExpr(&mut self, re: &str) -> AppliedId {
        trace!("addExpr {re}");
        let re = RecExpr::parse(re).unwrap();
        trace!("addExpr re {re:?}");
        self.add_expr(re)
    }

    pub fn add_expr(&mut self, re: RecExpr<L>) -> AppliedId {
        trace!("add_expr {re:?}");
        let mut n = re.node;
        let mut refs: Vec<&mut AppliedId> = n.applied_id_occurrences_mut();
        if CHECKS {
            assert_eq!(re.children.len(), refs.len());
        }
        // recursively add children
        for (i, child) in re.children.into_iter().enumerate() {
            *(refs[i]) = self.add_expr(child);
        }

        let nSorted = n.sorted();
        let ret = self.add(&n);

        let lenBefore = self.total_number_of_nodes();
        let sortedAppId = self.add(&nSorted);

        if self.total_number_of_nodes() != lenBefore {
            self.union_justified(&ret, &sortedAppId, Some("add_expr, sorted".to_owned()));
        }

        trace!("add_expr ret {ret:?}");
        ret
    }

    pub fn add(&mut self, enode: &L) -> AppliedId {
        debug!(
            "add enode {enode:?}
{:?}",
            enode.weak_shape()
        );
        // TODO: shape here can make children duplicate
        // e.g. [f(a, b), f(b, a)] might have shape [f(a, b), f(a, b)]
        // this does not maintain the deduplicate invariant
        let sh = self.shape_called_from_add(enode);
        let addedId = self.add_internal(&sh);
        addedId
    }

    // create a duplicate Enode with reset mapped slot in AppliedId,
    // the information of mapping to old one is in the returned Bijection
    fn shape_called_from_add(&self, enode: &L) -> (L, Bijection) {
        let ret = self.shape(enode);
        ret
    }

    // self.add(x) = y implies that x.slots() is a superset of y.slots().
    // x.slots() - y.slots() are redundant slots.
    pub(in crate::egraph) fn add_internal(&mut self, t: &(L, SlotMap)) -> AppliedId {
        trace!("add_internal {t:?}");
        let weakShapeEnodeId = self.getOrAddENodeId(&t.0);
        let lookupRes = self.lookup_internal((weakShapeEnodeId, t.1.clone()));
        trace!("lookup {t:?} -> {lookupRes:?}");
        if let Some(x) = lookupRes {
            return x;
        }
        let shapeENodeId = self.getOrAddENodeId(&self.shape(&t.0).0);

        trace!("lookup no result {t:?}");

        if CHECKS {
            assert!(
                self.syn_hashcons.get(&weakShapeEnodeId).is_none(),
                "shape exist in syn hashcons: {:?}",
                t
            );
        }

        // TODO this code is kinda exactly what add_syn is supposed to do anyways. There's probably a way to write this more concisely.
        // We convert the enode to "syn" so that semantic_add will compute the necessary redundancy proofs.
        // change private slot, apply slot map to Enode
        let enode = t.0.refresh_private().apply_slotmap(&t.1);
        if CHECKS {
            let enodeWeakShape = enode.weak_shape();
            // let weakShapeEnodeId = self.getENodeId(&enodeWeakShape.0);
            let synHashconsResult = self.syn_hashcons.get(&weakShapeEnodeId);
            let shape = self.shape(&enode);

            assert!(
                synHashconsResult.is_none(),
                "found weak_shape in syn_hashcons: {:?}\n
orig {:?}\n
orig_weak_shape {:?}\n
shape {:?}\n
in syn hashcons: {:?}\n
lookup shape result in hashcons: {:?}
lookup weak_shape result in hashcons: {:?}
",
                enodeWeakShape,
                enode,
                enode.orig_weak_shape(),
                shape,
                synHashconsResult,
                self.getHashcons(shapeENodeId),
                self.getHashcons(weakShapeEnodeId),
            );

            assert!(self.getHashcons(weakShapeEnodeId).is_none());
            assert!(self.syn_hashcons.get(&weakShapeEnodeId).is_none());
        }
        // println!("enode before = {:?}", enode.weak_shape().0);
        // assert!(self.semifyEnode(enode.clone()) == self.synify_enode(enode.clone()));
        // TODO: Pond why we dont need this?
        // let enode = self.synify_enode(enode);
        // let enode = self.semifyEnode(enode);
        // println!("enode after = {:?}", enode.weak_shape().0);

        // make takes up most of the time here
        let syn = self.mk_singleton_class(&enode);
        trace!("add_internal ret {syn:?}");
        syn
        // TODO: Pond why we dont need this?
        // let semifyAppId = self.semify_app_id(syn);
        // semifyAppId
    }

    pub fn lookupMut(&mut self, n: &L) -> Option<AppliedId> {
        let (enodeShape, bij) = self.shape(n);
        let enodeId = self.getOrAddENodeId(&enodeShape);
        self.lookup_internal((enodeId, bij))
    }

    pub fn lookup(&self, n: &L) -> Option<AppliedId> {
        let (enodeShape, bij) = self.shape(n);
        let enodeShapeId = self.getENodeId(&enodeShape).unwrap();
        self.lookup_internal((enodeShapeId, bij))
    }

    pub fn lookupPatternWithSubst(&self, pattern: &Pattern<L>, subst: &Subst) -> Option<AppliedId> {
        match pattern {
            Pattern::ENode(n, children) => {
                let mut n = n.clone();
                let mut refs = n.applied_id_occurrences_mut();
                if CHECKS {
                    assert_eq!(children.len(), refs.len());
                }
                for i in 0..refs.len() {
                    let result = self.lookupPatternWithSubst(&children[i], subst);
                    if result.is_none() {
                        return None;
                    }
                    *(refs[i]) = result.unwrap();
                }
                self.lookup(&n)
            }
            Pattern::PVar(v) => {
                return subst.get(v).cloned();
            }
            _ => {
                panic!()
            }
        }
    }

    pub fn lookupExpr(&self, re: &str) -> Option<AppliedId> {
        let re = RecExpr::parse(re).unwrap();
        self.lookupRecExpr(re)
    }

    // TODO: this can't sort mew ENode?
    pub fn lookupRecExpr(&self, re: RecExpr<L>) -> Option<AppliedId> {
        let mut n = re.node.clone();
        let mut refs: Vec<&mut AppliedId> = n.applied_id_occurrences_mut();
        if CHECKS {
            assert_eq!(re.children.len(), refs.len());
        }
        for (i, child) in (re.children.clone()).into_iter().enumerate() {
            let childRes = self.lookupRecExpr(child);
            if childRes.is_none() {
                return None;
            }
            *(refs[i]) = childRes.unwrap();
        }
        let n = n.sorted();
        let ret = self.lookup(&n);
        ret
    }

    pub fn lookupRecExprMut(&mut self, re: RecExpr<L>) -> Option<AppliedId> {
        let mut n = re.node.clone();
        let mut refs: Vec<&mut AppliedId> = n.applied_id_occurrences_mut();
        if CHECKS {
            assert_eq!(re.children.len(), refs.len());
        }
        for (i, child) in (re.children.clone()).into_iter().enumerate() {
            let childRes = self.lookupRecExprMut(child);
            if childRes.is_none() {
                return None;
            }
            *(refs[i]) = childRes.unwrap();
        }
        let n = n.sorted();
        let ret = self.lookupMut(&n);
        ret
    }

    pub(in crate::egraph) fn lookup_internal(
        &self,
        (enodeId, n_bij): (ENodeId, Bijection),
    ) -> Option<AppliedId> {
        // let enodeId = self.getENodeId(shape);
        // if enodeId.is_none() {
        //     return None;
        // }
        // let enodeId = enodeId.unwrap();
        let i: Option<Id> = self.getHashcons(enodeId);
        if i.is_none() {
            // let synResult = self.syn_hashcons.get(&shape);
            // if synResult.is_none() {
            //     return None;
            // } else {
            //     let synResult = synResult.unwrap();
            //     let updatedSynResult = self.find_applied_id(synResult);
            //     i = Some(updatedSynResult.id);
            // }

            return None;
        }
        let i = &i.unwrap();
        let c = &self.classes[i];
        let cn_bij = &c.nodes[&enodeId].elem;

        // X = shape.slots()
        // Y = n.slots()
        // Z = c.slots()
        // n_bij :: X -> Y
        // cn_bij :: X -> Z
        // out :: Z -> Y
        let out = cn_bij.inverse().compose(&n_bij);

        // Note that ENodes in an EClass can have redundant slots.
        // They shouldn't come up in the AppliedId.
        let out = out.iter().filter(|(x, _)| c.slots.contains(x)).collect();

        let app_id = self.mk_sem_applied_id(*i, out);

        if CHECKS {
            assert_eq!(&c.slots, &app_id.m.keys_set());
        }

        Some(app_id)
    }

    pub fn getExactENodeInEGraph(&self, n: &L) -> L {
        let (shape, _) = &self.shape(n);
        let enodeId = self.getENodeId(shape);
        let i = self.getHashcons(enodeId.unwrap()).unwrap();
        let c = &self.classes[&i];
        let cn_bij = &c.nodes[&enodeId.unwrap()].elem;
        shape.apply_slotmap(cn_bij)
    }

    pub fn getExactENodeInEClass(&self, n: &L, i: &Id) -> L {
        let (shape, _) = &self.shape(n);
        let enodeId = self.getENodeId(shape);
        let c = &self.classes[&i];
        let cn_bij = &c.nodes[&enodeId.unwrap()].elem;
        shape.apply_slotmap(cn_bij)
    }
}

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    // returns a syn applied id.
    fn mk_singleton_class(&mut self, syn_enode: &L) -> AppliedId {
        let old_slots = syn_enode.slots();

        let fresh_to_old = Bijection::bijection_from_fresh_to(&old_slots);
        let old_to_fresh = fresh_to_old.inverse();

        // allocate new class & slot set.
        let fresh_slots = old_to_fresh.values_set();
        // now the variables input to syn_enode are fresh slots
        let syn_enode_fresh = syn_enode.apply_slotmap_fresh(&old_to_fresh);

        // create Eclass?
        let i = self.alloc_eclass(&fresh_slots, &syn_enode_fresh);

        // we use semantic_add so that the redundancy, symmetry and congruence checks run on it.
        let t = syn_enode_fresh.weak_shape();
        // let t = self.shape(&syn_enode_fresh);
        let enodeId = self.getOrAddENodeId(&t.0);
        self.raw_add_to_class(i, (enodeId, t.1), i);
        let enodeId = self.getOrAddENodeId(&t.0);
        self.pending.insert(enodeId, PendingType::Full);
        self.modify_queue.push(i);
        // self.rebuild_called_from_add();

        // fresh slots is for that eclass, old is slots from added Enode
        self.mk_syn_applied_id(i, fresh_to_old)
    }

    #[allow(unused)]
    fn rebuild_called_from_add(&mut self) {
        self.rebuild();
    }

    // adds (sh, bij) to the eclass `id`.
    // TODO src_id should be optional!
    pub(in crate::egraph) fn raw_add_to_class(
        &mut self,
        id: Id,
        (enodeId, bij): (ENodeId, Bijection),
        src_id: Id,
    ) {
        // debug!("raw_add_to_class: add to class {id:?} {:?}", sh);
        let psn = ProvenSourceNode {
            elem: bij.clone(),
            src_id,
        };

        let tmp1 = self
            .classes
            .get_mut(&id)
            .unwrap()
            .nodes
            .insert(enodeId, psn);

        if CHECKS {
            // assert!(self.semifyEnode(sh.clone()) == sh)
        }
        // synified version is added to hashcons from self.add
        // non-synified version is added to hashcons from self.handle_pending
        let tmp2 = self.setHashcons(enodeId, id);
        if CHECKS {
            // hashcons should contain semify enode
            assert!(tmp1.is_none());
            assert!(tmp2.is_none());
        }
        let sh = self.getENode(enodeId);
        trace!(
            "insert to hashcons\n
{sh:?}\n
orig {:?}\n
shape {:?}\n
orig_weak_shape {:?}\n
 -> {id:?}",
            sh.apply_slotmap(&bij),
            self.shape(&sh),
            sh.orig_weak_shape()
        );
        for ref_id in sh.ids() {
            // if ref_id == Id(46957) {
            //     println!(
            //         "raw_add_to_class enodeId {enodeId:?} enode {sh:?}, use {:?}",
            //         ref_id
            //     );
            // }
            let usages = &mut self.classes.get_mut(&ref_id).unwrap().usagesMut();
            usages.insert(enodeId);
        }
    }

    // TODO: change this to pass enodeId?
    pub(in crate::egraph) fn raw_remove_from_class(
        &mut self,
        id: Id,
        enodeId: ENodeId,
    ) -> ProvenSourceNode {
        let opt_psn = self.classes.get_mut(&id).unwrap().nodes.remove(&enodeId);
        let opt_id = self.removeFromHashcons(enodeId);
        let sh = self.getENode(enodeId);

        trace!(
            "remove from hashcons\n
orig_weak_shape {:?}\n
{:?}\n
 -> {opt_id:?}",
            sh.orig_weak_shape(),
            sh
        );
        if CHECKS {
            assert!(opt_psn.is_some());
            assert!(opt_id.is_some());
        }
        for ref_id in sh.ids() {
            let usages = &mut self.classes.get_mut(&ref_id).unwrap().usagesMut();
            usages.remove(&enodeId);
        }

        opt_psn.unwrap()
    }
}

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    // TODO make the public API auto "fresh" slots.
    #[allow(unused_variables)]
    pub fn alloc_empty_eclass(&mut self, slots: &SmallHashSet<Slot>) -> Id {
        panic!("Can't use alloc_empty_eclass if explanations are enabled!");
    }

    pub(in crate::egraph) fn alloc_eclass(
        &mut self,
        slots: &SmallHashSet<Slot>,
        syn_enode: &L,
    ) -> Id {
        trace!("alloc_eclass {syn_enode:?}");
        let c_id = Id(self.unionfind_len()); // Pick the next unused Id.

        let syn_slots = syn_enode.slots();
        let proven_perm =
            ProvenPerm::identity(c_id, &slots, &syn_slots, self.proof_registry.clone());

        let c = EClass::new(
            BTreeMap::default(),
            slots.clone(),
            BTreeSet::default(),
            Group::identity(&proven_perm),
            syn_enode.clone(),
            N::make(&self, &syn_enode, &slots.clone().into()),
        );
        self.classes.insert(c_id, c);

        {
            // add syn_enode to the hashcons.
            // bij will map shapeEnode to oldSlot
            let (sh, bij) = syn_enode.weak_shape();
            let enodeId = self.getOrAddENodeId(&sh);

            if CHECKS {
                if self.syn_hashcons.contains_key(&enodeId) {
                    panic!("syn_hashcons already contains key {:?}", sh);
                }
            }

            // make new apply id
            let app_id = self.mk_syn_applied_id(c_id, bij.inverse());
            // by applying app_id to this Eclass, there will be one Enode in the eclass that matches shape
            // because this appliedId is created from inverse of bijection
            trace!(
                "insert weak_shape to syn_hashcons\n
{sh:?}\n
orig {syn_enode:?}\n
shape {:?}\n
orig_weak_shape {:?}\n
-> {app_id:?}",
                self.shape(&syn_enode),
                syn_enode.orig_weak_shape()
            );
            self.syn_hashcons.insert(enodeId, app_id);
        }

        let syn_app_id = self.mk_syn_identity_applied_id(c_id);
        trace!("syn_app_id {syn_app_id:?}");
        let pai = self.refl_pai(&syn_app_id);
        trace!("call unionfind_set from alloc_eclass {c_id:?} {pai:?}");
        self.unionfind_set(c_id, pai);

        c_id
    }
}
