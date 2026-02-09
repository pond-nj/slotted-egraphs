use crate::*;

mod find;
pub use find::*;

mod add;
pub use add::*;

mod union;
use nauty_Traces_sys::{empty_graph, ADDONEEDGE, SETWORDSNEEDED};
pub use union::*;

mod rebuild;
pub use rebuild::*;

mod check;
pub use check::*;

mod analysis;
pub use analysis::*;
use vec_collections::AbstractVecSet;

use core::fmt;
use derive_more::Debug;
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    fmt::*,
    io,
};

mod print;

mod eclass;
pub use eclass::*;

use log::{debug, error, trace, warn};
pub use print::*;

mod shape;
pub use shape::*;

// invariants:
// 1. If two ENodes (that are in the EGraph) have equal .shape(), they have to be in the same eclass.
// 2. enode.slots() is always a superset of c.slots, if enode is within the eclass c.
//    if ENode::Lam(si) = enode, then we require i to not be in c.slots.
//    In practice, si will always be Slot(0).
// 3. AppliedId::m is always a bijection. (eg. c1(s0, s1, s0) is illegal!)
//    AppliedId::m also always has the same keys as the class expects slots.
// 4. Slot(0) should not be in EClass::slots of any class.
/// A datastructure to efficiently represent congruence relations on terms with binders.
pub struct EGraph<L: Language, N: Analysis<L> = ()> {
    // an entry (l, r(sa, sb)) in unionfind corresponds to the equality l(s0, s1, s2) = r(sa, sb), where sa, sb in {s0, s1, s2}.
    // normalizes the eclass.
    // Each Id i that is an output of the unionfind itself has unionfind[i] = (i, identity()).

    // We use RefCell to allow for inter mutability, so that find(&self) can do path compression.
    unionfind: RefCell<Vec<ProvenAppliedId>>,

    // if a class does't have unionfind[x].id = x, then it doesn't contain nodes / usages.
    // It's "shallow" if you will.
    pub(crate) classes: BTreeMap<Id, EClass<L, N>>,

    // For each shape contained in the EGraph, maps to the EClass that contains it.
    hashcons: BTreeMap<L, Id>,

    // For each (syn_slotset applied) non-normalized (i.e. "syntactic") weak shape, find the e-class who has this as syn_enode.
    // TODO remove this if explanations are disabled.
    syn_hashcons: BTreeMap<L, AppliedId>,

    // E-Nodes that need to be re-processed, stored as shapes.
    pending: BTreeMap<L, PendingType>,

    // TODO remove this if explanations are disabled.
    pub(crate) proof_registry: ProofRegistry,

    pub(crate) subst_method: Option<Box<dyn SubstMethod<L, N>>>,

    pub analysis: N,

    // N::modify(_) will be run on these classes.
    // We delay handling modify so that all invariants can be rebuild again, first.
    modify_queue: Vec<Id>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum PendingType {
    OnlyAnalysis, // only analysis needs to be updated.
    Full,         // the e-node, it's strong shape & the analysis need to be updated.
}

impl<L: Language, N: Analysis<L> + Default> Default for EGraph<L, N> {
    fn default() -> Self {
        EGraph::new(N::default())
    }
}

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    /// Creates an empty e-graph.
    pub fn new(analysis: N) -> Self {
        Self::with_subst_method::<SynExprSubst>(analysis)
    }

    /// Creates an empty e-graph, while specifying the substitution method to use.
    pub fn with_subst_method<S: SubstMethod<L, N>>(analysis: N) -> Self {
        EGraph {
            unionfind: Default::default(),
            classes: Default::default(),
            hashcons: Default::default(),
            syn_hashcons: Default::default(),
            pending: Default::default(),
            proof_registry: ProofRegistry::default(),
            subst_method: Some(S::new_boxed()),
            analysis,
            modify_queue: Vec::new(),
        }
    }

    // TODO: include eclass slots
    pub fn allSlots(&self, id: Id) -> BTreeSet<Slot> {
        let c = self.eclass(id).unwrap();
        let mut totalSlots = BTreeSet::default();
        for (sh, psn) in &c.nodes {
            let node = sh.apply_slotmap(&psn.elem);
            totalSlots.extend(node.slots().into_iter());
        }

        totalSlots.extend(self.slots(id));

        totalSlots
    }

    pub fn slots(&self, id: Id) -> SmallHashSet<Slot> {
        self.classes[&id].slots.clone()
    }

    // slot of syn_enode
    pub(crate) fn syn_slots(&self, id: Id) -> SmallHashSet<Slot> {
        self.classes[&id].syn_enode().slots()
    }

    pub fn analysis_data(&self, i: Id) -> &N::Data {
        &self.classes[&self.find_id(i)].analysis_data
    }

    pub fn analysis_data_mut(&mut self, i: Id) -> &mut N::Data {
        &mut self
            .classes
            .get_mut(&self.find_id(i))
            .unwrap()
            .analysis_data
    }

    pub fn eclass(&self, i: Id) -> Option<&EClass<L, N>> {
        self.classes.get(&self.find_id(i))
    }

    // should use .ids() instead
    // pub fn eclasses(&self) -> &BTreeMap<Id, EClass<L, N>> {
    //     &self.classes
    // }

    // get node with this shape using the eclass appId
    pub fn getNode(&self, eclassAppId: &AppliedId, node: &L) -> L {
        let eclass = self.eclass(eclassAppId.id).unwrap();
        debug!("eclass {:?}", eclass);

        // update node
        let node = self.find_enode(node);

        let (sh, _) = node.weak_shape();
        let Some(eclassNode) = eclass.nodes.get(&sh) else {
            panic!("node {node:?} not found in {eclass:#?}");
        };
        let l = sh.apply_slotmap(&eclassNode.elem);
        debug!("before apply_slotmap_intersect {l:?}");
        debug!("eclassAppId.m {:#?}", eclassAppId.m);
        l.apply_slotmap_partial(&eclassAppId.m)
    }

    pub fn enodes(&self, i: Id) -> BTreeSet<L> {
        // We prevent this, as otherwise the output will have wrong slots.
        assert!(self.is_alive(i), "Can't access e-nodes of dead class");

        self.classes[&i]
            .nodes
            .iter()
            .map(|(x, psn)| x.apply_slotmap(&psn.elem))
            .collect()
    }

    // Generates fresh slots for redundant slots.
    pub fn enodes_applied(&self, i: &AppliedId) -> Vec<L> {
        // assert!(self.is_alive(i.id));
        let class = &self.classes[&i.id];
        let class_slots = &class.slots;

        let mut result = Vec::with_capacity(class.nodes.len());
        if class.nodes.len() == 0 {
            error!("class.nodes is empty");
            error!("class {}: {:?}", i.id, class);
            error!("unionfind {} -> {:?}", i.id, self.unionfind_get(i.id));
            assert!(class.nodes.len() > 0);
        }

        for (x, psn) in &class.nodes {
            let mut x = x.apply_slotmap(&psn.elem);

            // (Pond) Create a mapping of unfound slots (of this enode) in eclass slots to fresh slots.
            let mut map: SmallHashMap<Slot, Slot> = SmallHashMap::default();
            for slot in x.all_slot_occurrences_mut() {
                // when does this happen?
                if !class_slots.contains(&slot) {
                    if let Some(v) = map.get(slot) {
                        *slot = *v;
                    } else {
                        let v = Slot::fresh();
                        map.insert(slot.clone(), v.clone());
                        *slot = v;
                    }
                }
            }

            // m contains unmapped slot from x
            let mut m = SlotMap::new();
            for slot in x.slots() {
                if !i.m.contains_key(slot) {
                    m.insert(slot, Slot::fresh());
                }
            }

            // m contains mapping from i
            // now m can completely map slots in x
            for (x, y) in i.m.iter() {
                m.insert(x, y);
            }

            x = x.apply_slotmap(&m);
            result.push(x);
        }

        result
    }

    // number of enodes in the egraph.
    pub fn total_number_of_nodes(&self) -> usize {
        self.hashcons.len()
    }

    pub fn totalNumberOfEclass(&self) -> usize {
        self.classes.len()
    }

    /// Checks that two AppliedIds are semantically equal.
    pub fn eq(&self, a: &AppliedId, b: &AppliedId) -> bool {
        let a = self.find_applied_id(a);
        let b = self.find_applied_id(b);

        if CHECKS {
            self.check_sem_applied_id(&a);
            self.check_sem_applied_id(&b);
        }

        if a.id != b.id {
            return false;
        }
        if a.m.values_set() != b.m.values_set() {
            return false;
        }
        let id = a.id;

        let perm = a.m.compose(&b.m.inverse());
        if CHECKS {
            assert!(perm.is_perm());
            assert_eq!(&perm.values_set(), &self.classes[&id].slots);
        }

        self.classes[&id].group().contains(&perm)
    }

    // refreshes all internal slots of l.
    pub(crate) fn refresh_internals(&self, l: &L) -> L {
        let i = self.lookup(l).unwrap();
        l.refresh_internals(i.slots())
    }

    // converts l to its class normal form, so that calling lookup on it yields the identity AppliedId.
    pub(crate) fn class_nf(&self, l: &L) -> L {
        let l = self.refresh_internals(l);
        let i = self.lookup(&l).unwrap();

        // needs to be `apply_slotmap_fresh` in case `l` has redundancies.
        let l = l.apply_slotmap_fresh(&i.m);

        if CHECKS {
            let identity = self.mk_sem_identity_applied_id(i.id);
            assert!(self.eq(&i, &identity));
        }

        l
    }

    /// Prints the contents of the E-Graph. Helpful for debugging.
    // pub fn dump<T: fmt::Write>(&self, f: &mut T) -> Result {
    //     write!(f, "\n == Egraph ==")?;
    //     let mut eclasses: Vec<(&Id, &EClass<L, N>)> = self.classes.iter().collect();
    //     eclasses.sort_by_key(|(x, _)| *x);

    //     for (i, c) in eclasses {
    //         write!(f, "\n{:?}(", i)?;
    //         c.dumpEClass(f)?;
    //     }
    //     write!(f, "")?;
    //     Ok(())
    // }

    // The resulting e-nodes are written as they exist in the e-class.
    pub(crate) fn usages(&self, i: Id) -> Vec<L> {
        let mut out = Vec::new();
        for x in self.classes[&i].usages() {
            let j = self.lookup(x).unwrap().id;
            let bij = &self.classes[&j].nodes[&x].elem;
            let x = x.apply_slotmap(bij);
            out.push(x);
        }
        out
    }

    // add mapping for slots from syn_enode
    pub(crate) fn synify_app_id(&self, app: AppliedId) -> AppliedId {
        let mut app = app;
        // get slot of syn_enode
        for s in self.syn_slots(app.id) {
            // app must contains mapping for slots of syn_enode
            if !app.m.contains_key(s) {
                app.m.insert(s, Slot::fresh());
            }
        }
        app
    }

    // make sure the pointer appliedId contains mapping for syn_enode in the children eclass
    #[allow(dead_code)]
    pub(crate) fn synify_enode(&self, enode: L) -> L {
        enode.map_applied_ids(|app| self.synify_app_id(app))
    }

    #[allow(dead_code)]
    pub(crate) fn semifyEnode(&self, enode: L) -> L {
        enode.map_applied_ids(|app| self.semify_app_id(app))
    }

    // undo the synify enode, remove the keys to just the slots of that eclass
    #[allow(dead_code)]
    pub(crate) fn semify_app_id(&self, app: AppliedId) -> AppliedId {
        let slots = self.slots(app.id);

        let mut app = app;
        for k in app.m.keys_set() {
            if !slots.contains(&k) {
                app.m.remove(k);
            }
        }

        assert!(app.m.keys_set() == slots, "{:?} vs {slots:?}", app.m);
        app
    }

    #[cfg(feature = "explanations")]
    pub(crate) fn semify_enode(&self, enode: L) -> L {
        enode.map_applied_ids(|app| self.semify_app_id(app))
    }

    #[allow(unused)]
    fn getENodeExprRecur<'a>(
        self: &'a Self,
        enode: &L,
        map: &'a mut BTreeMap<AppliedId, RecExpr<L>>,
    ) -> &'a RecExpr<L> {
        let cs: Vec<RecExpr<L>> = (*enode)
            .applied_id_occurrences()
            .iter()
            .map(|x| self.get_syn_expr(x))
            .collect::<Vec<_>>();

        let ret = RecExpr {
            node: nullify_app_ids(enode),
            children: cs,
        };

        let eclassId = self.lookup(enode).unwrap();
        map.insert(eclassId.clone(), ret);

        map.get(&eclassId).unwrap()
    }

    fn getSynExprRecur<'a>(
        self: &'a Self,
        i: &AppliedId,
        map: &'a mut BTreeMap<AppliedId, RecExpr<L>>,
    ) -> &'a RecExpr<L> {
        if map.contains_key(i) {
            // println!("{} -> {}", i, map[i]);
            return map.get(i).unwrap();
        }
        let enode = self.get_syn_node(i);
        // println!("syn enode {i:?} {enode:?}");
        let cs = enode
            .applied_id_occurrences()
            .iter()
            .map(|x| self.get_syn_expr(x))
            .collect();

        let ret = RecExpr {
            node: nullify_app_ids(&enode),
            children: cs,
        };

        map.insert(i.clone(), ret);

        map.get(i).unwrap()
    }

    pub fn getSynExpr<'a>(
        self: &'a Self,
        i: &Id,
        map: &'a mut BTreeMap<AppliedId, RecExpr<L>>,
    ) -> &'a RecExpr<L> {
        let appId = self.mk_sem_identity_applied_id(i.clone());
        // println!("identity app id {i:?} -> {appId:?}");
        self.getSynExprRecur(&appId, map)
    }

    /// Returns the canonical term corresponding to `i`.
    ///
    /// This function will use [EGraph::get_syn_node] repeatedly to build up this term.
    pub fn get_syn_expr(&self, i: &AppliedId) -> RecExpr<L> {
        let enode = self.get_syn_node(i);
        let cs = enode
            .applied_id_occurrences()
            .iter()
            .map(|x| self.get_syn_expr(x))
            .collect();
        RecExpr {
            node: nullify_app_ids(&enode),
            children: cs,
        }
    }

    /// Returns the canonical e-node corresponding to `i`.
    pub fn get_syn_node(&self, i: &AppliedId) -> L {
        let syn_enode = &self.classes[&i.id].syn_enode();
        let syn = self.find_enode(syn_enode);

        let _syn_slots = syn.slots();
        // if !i.m.keys().is_superset(&syn_slots) {
        //     println!("i = {:?}", i);
        //     println!("eclass {:?}", self.eclass(i.id));
        //     println!("syn_slots = {syn_slots:?}");
        //     println!("i.m = {:?}", i.m);
        // }
        syn.apply_slotmap_partial(&i.m)
    }

    pub fn getSynNodeNoSubst(&self, i: &Id) -> &L {
        &self.classes[i].syn_enode()
    }

    pub fn getSlotPermutation(&self, i: &Id) -> Vec<SlotMap> {
        let c = self.eclass(*i).unwrap();
        c.group().generators().into_iter().map(|x| x.elem).collect()
    }
}

impl PendingType {
    pub(crate) fn merge(self, other: PendingType) -> PendingType {
        match (self, other) {
            (PendingType::Full, _) => PendingType::Full,
            (_, PendingType::Full) => PendingType::Full,
            (PendingType::OnlyAnalysis, PendingType::OnlyAnalysis) => PendingType::OnlyAnalysis,
        }
    }
}

// {1,2} x {3} x {4,5} -> (1,3,4), (1,3,5), (2,3,4), (2,3,5)
fn cartesian<'a, T>(input: &'a [Vec<T>]) -> impl Iterator<Item = Vec<&'a T>> + use<'a, T> {
    let n = input.len();
    let mut indices = vec![0; n];
    let mut done = false;

    // let mut expectOutLen = 1;
    // for i in 0..n {
    //     expectOutLen *= input[i].len();
    // }

    // println!("cartesian expectOutLen {}", expectOutLen);

    let f = move || {
        if done {
            return None;
        }
        let out: Vec<&T> = (0..n).map(|i| &input[i][indices[i]]).collect();
        for i in 0..n {
            indices[i] += 1;
            if indices[i] >= input[i].len() {
                indices[i] = 0;
            } else {
                return Some(out);
            }
        }
        done = true;
        Some(out)
    };
    std::iter::from_fn(f)
}

#[test]
fn cartesian1() {
    let v = [vec![1, 2], vec![3], vec![4, 5]];
    let vals = cartesian(&v);
    assert_eq!(vals.count(), 4);
}
