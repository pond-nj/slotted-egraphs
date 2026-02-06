use std::collections::{BTreeMap, BTreeSet};

use crate::*;
use log::{debug, error, trace};
use vec_collections::AbstractVecSet;

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    // mk_sem_applied_id & friends.
    #[track_caller]
    pub(crate) fn mk_sem_applied_id(&self, i: Id, m: SlotMap) -> AppliedId {
        let app_id = AppliedId::new(i, m);

        if CHECKS {
            self.check_sem_applied_id(&app_id);
        }

        app_id
    }

    // public API:
    #[track_caller]
    pub fn mk_identity_applied_id(&self, i: Id) -> AppliedId {
        self.mk_sem_identity_applied_id(i)
    }

    // (Pond) turn id (of this eclass) to AppliedId with identity slotmap
    #[track_caller]
    pub fn mk_sem_identity_applied_id(&self, i: Id) -> AppliedId {
        let slots = self.slots(i);
        self.mk_sem_applied_id(i, SlotMap::identity(&slots))
    }

    #[track_caller]
    pub(crate) fn check_sem_applied_id(&self, app_id: &AppliedId) {
        app_id.check();
        assert_eq!(
            self.slots(app_id.id),
            app_id.m.keys_set(),
            "checking sem AppliedId failed: Wrong key-set, {app_id:?}"
        );
    }

    // mk_syn_applied_id & friends.
    #[track_caller]
    pub(crate) fn mk_syn_applied_id(&self, i: Id, m: SlotMap) -> AppliedId {
        let app_id = AppliedId::new(i, m);

        if CHECKS {
            self.check_syn_applied_id(&app_id);
        }

        app_id
    }

    #[track_caller]
    pub(crate) fn mk_syn_identity_applied_id(&self, i: Id) -> AppliedId {
        self.mk_syn_applied_id(i, SlotMap::identity(&self.syn_slots(i)))
    }

    #[track_caller]
    pub(crate) fn check_syn_applied_id(&self, app_id: &AppliedId) {
        app_id.check();
        assert_eq!(
            self.syn_slots(app_id.id),
            app_id.m.keys_set(),
            "checking syn AppliedId failed: Wrong key-set, {app_id:?}"
        );
    }

    pub fn check(&self) {
        // Checks whether the hashcons / usages are correct.
        // And also checks that each Shape comes up in at most one EClass!
        let mut hashcons = BTreeMap::default();
        let mut usages = BTreeMap::default();

        for (i, _) in &self.classes {
            usages.insert(*i, BTreeSet::default());
        }

        // println!("{}", self);

        // redundancy-check for leaders.
        // TODO add a similar check for followers, using unionfind_get.
        for (i, _) in &self.classes {
            if !self.is_alive(*i) {
                continue;
            }

            // There should be no symmetries witnessed by the unionfind.
            // It would make stuff just weird.
            let sem = self.mk_sem_identity_applied_id(*i);
            let sem2 = self.find_applied_id(&sem);
            assert_eq!(sem, sem2);

            #[cfg(feature = "explanations")]
            {
                let c = &self.classes[i];
                let eq = self.proven_unionfind_get(*i).proof.equ();
                // eq.l.m :: slots(i) -> X
                // eq.r.m :: slots(i) -> X
                let tmp = eq.l.m.compose_intersect(&eq.r.m.inverse());
                assert!(tmp.is_perm());
                assert_eq!(c.slots, tmp.keys());
                assert_eq!(c.slots, tmp.values());
            }
        }

        for (i, c) in &self.classes {
            for sh in c.nodes.keys() {
                assert!(!hashcons.contains_key(sh));
                hashcons.insert(sh.clone(), *i);

                for ref_id in sh.ids() {
                    usages.get_mut(&ref_id).unwrap().insert(sh.clone());
                }
            }
        }

        assert_eq!(hashcons, self.hashcons);
        for (i, c) in &self.classes {
            assert_eq!(&usages[&i], c.usages());
        }

        for (_, c) in &self.classes {
            for p in c.group().all_perms() {
                p.check();
            }
        }

        // check that self.classes contains exactly these classes which point to themselves in the unionfind.
        let all_keys = self
            .unionfind_iter()
            .map(|(x, _)| x)
            .collect::<BTreeSet<_>>();
        let all_values = self
            .unionfind_iter()
            .map(|(_, x)| x.id)
            .collect::<BTreeSet<_>>();
        let all_classes = self.classes.keys().copied().collect::<BTreeSet<_>>();
        let all: BTreeSet<Id> = &(&all_keys | &all_values) | &all_classes;
        for i in all {
            // if they point to themselves, they should do it using the identity.
            if self.is_alive(i) {
                assert_eq!(self.unionfind_get(i), self.mk_sem_identity_applied_id(i));
            } else {
                assert!(self.classes[&i].nodes.is_empty());
                for sh in self.classes[&i].usages() {
                    assert_eq!(self.pending.get(&sh), Some(&PendingType::Full));
                }
            }
        }

        // check that no EClass has Slot(0) in its API.
        for (_, c) in &self.classes {
            assert!(!c.slots.contains(&Slot::numeric(0)));
        }

        // Check that the Unionfind has valid AppliedIds.
        for (_, app_id) in self.unionfind_iter() {
            check_internal_applied_id::<L, N>(self, &app_id);
        }

        // Check that all ENodes are valid.
        for (cid, c) in &self.classes {
            for (sh, ProvenSourceNode { elem: bij, .. }) in &c.nodes {
                let real = sh.apply_slotmap(bij);
                assert!(real.slots().is_superset(&c.slots));

                if self.pending.get(&sh) == Some(&PendingType::Full) {
                    continue;
                }

                // shape, computed from permutation of slots in appliedId from permutation
                // in children eclasses
                let (computed_sh, computed_bij) = self.shape(&real);
                let weak_shape = real.weak_shape();
                trace!(
                    "weak_shape {real:?} -> {:?} {:?}",
                    weak_shape.0,
                    weak_shape.1
                );
                trace!("weak shape of {sh:?} <-> {:?}", sh.orig_weak_shape());
                assert_eq!(&computed_sh, sh);

                // computed_bij :: shape-slots -> slots(i)
                // bij :: shape-slots -> slots(i)
                let perm = computed_bij.inverse().compose_intersect(&bij);

                // permutation in this group
                let perm = perm
                    .iter()
                    .filter_map(|(x, y)| {
                        if c.slots.contains(&x) && c.slots.contains(&y) {
                            Some((x, y))
                        } else {
                            None
                        }
                    })
                    .collect();

                if !c.group().contains(&perm) {
                    error!("");
                    error!("egraph {self:?}");
                    error!("sh {sh:?}");
                    let (_, _) = self.shape(&real);
                    error!("computed bij {:?}", computed_bij);
                    error!("computed bij inverse {:?}", computed_bij.inverse());
                    error!("bij {:?}", bij);
                    error!(
                        "computed_bij.inverse().compose_intersect(&bij) = perm {:?}",
                        perm
                    );
                    error!("all perms {:?}", c.group().all_perms());
                    error!("eclass {cid} {:?}", c);
                    error!("c.group {:?}", c.group());
                    error!("");
                }

                assert!(c.group().contains(&perm));

                for x in real.applied_id_occurrences() {
                    check_internal_applied_id::<L, N>(self, &x);
                }
            }
        }

        pub fn check_internal_applied_id<L: Language, N: Analysis<L>>(
            eg: &EGraph<L, N>,
            app_id: &AppliedId,
        ) {
            // 1. the app_id needs to be normalized!
            let y = eg.find_applied_id(app_id);
            assert_eq!(app_id, &y);

            // 2. It needs to have exactly the same slots as the underlying EClass.
            assert_eq!(&app_id.m.keys_set(), &eg.classes[&app_id.id].slots);
        }

        // TODO: check sorted
        // for (cid, c) in &self.classes {
        //     for (sh, psn) in &c.nodes {
        //         let node = sh.apply_slotmap(&psn.elem);
        //         let (sh, m) = node.weak_shape();

        //         let sortedNode = node.sorted();
        //         let lookupSortedRes = self.lookup_internal(&self.shape(&sortedNode));
        //         if lookupSortedRes.is_some() {
        //             assert_eq!(*cid, lookupSortedRes.unwrap().id);
        //         }
        //     }
        // }
    }
}
