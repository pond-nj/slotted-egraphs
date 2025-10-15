#![allow(non_snake_case)]
use crate::{rewrite::pattern, *};
use core::panic;
use log::debug;
use log_derive::{logfn, logfn_inputs};

pub type Subst = HashMap<String, AppliedId>;

#[derive(Default, Clone, Debug)]
struct State {
    // uses egraph slots.
    partial_subst: Subst,

    // maps from the egraph slots to the pattern slots.
    partial_slotmap: SlotMap,
}

pub fn mergeSubst(subst1: &mut Subst, subst2: &Subst) {
    // let mut newSubst = subst1.clone();
    for s in subst2 {
        assert!(!subst1.contains_key(s.0));
        subst1.insert(s.0.clone(), s.1.clone());
    }
}

pub fn ematch_all<L: Language, N: Analysis<L>>(
    eg: &EGraph<L, N>,
    pattern: &Pattern<L>,
) -> Vec<Subst> {
    debug!("=== Call EmatchAll ===");
    debug!("pattern = {pattern}");
    let mut out: Vec<Subst> = Vec::new();
    for i in eg.ids() {
        let i = eg.mk_sem_identity_applied_id(i);
        let result = ematchAllInEclassInternal(pattern, State::default(), i, eg);
        out.extend(result.into_iter().map(final_subst));
    }
    // assert!(out.len() == outPatterns.len());
    out
}

pub fn ematchAllInEclass<L: Language, N: Analysis<L>>(
    eg: &EGraph<L, N>,
    pattern: &Pattern<L>,
    id: Id,
) -> Vec<Subst> {
    let mut out: Vec<Subst> = Vec::new();
    let i = eg.mk_sem_identity_applied_id(id);
    let result = ematchAllInEclassInternal(pattern, State::default(), i, eg);
    out.extend(result.into_iter().map(final_subst));
    out
}

// (Pond) deal with Pattern cases and find Enode with same type
// `i` uses egraph slots instead of pattern slots.
// (Pond) Find pattern of that type in the eclass
fn ematchAllInEclassInternal<L: Language, N: Analysis<L>>(
    pattern: &Pattern<L>,
    st: State,
    i: AppliedId,
    eg: &EGraph<L, N>,
) -> Vec<State> {
    match &pattern {
        Pattern::PVar(v) => {
            let mut st = st;
            if let Some(j) = st.partial_subst.get(v) {
                if !eg.eq(&i, j) {
                    debug!("continue because mismatch mapped var {:?} != {:?}", i, j);
                    return Vec::new();
                } else {
                    debug!("check existing var {:?}, pass", i);
                }
            } else {
                debug!("insert {} -> {:?} to subst", v, i);
                st.partial_subst.insert(v.clone(), i.clone());
            }
            let ret = vec![st];
            debug!("Search {} in {}", pattern, i);
            debug!("Search pattern {:?}", pattern);
            debug!("ret {:?}", ret);
            ret
        }
        Pattern::ENode(patternEnode, patternChildren) => {
            let mut out = Vec::new();
            let enodesInEclass = eg.enodes_applied(&i);
            debug!("Search {} in {:?}", pattern, i);
            debug!("Search pattern {:?}", pattern);
            debug!("enodesInEclass at {}, {:?}", i, enodesInEclass);
            for enode in enodesInEclass.clone() {
                // (Pond) n is from a pattern, nn is an enode.
                // (Pond) find the same type of Enode.
                let d = std::mem::discriminant(patternEnode);
                let dd = std::mem::discriminant(&enode);
                if d != dd {
                    debug!("continue because of discriminant mismatch");
                    continue;
                };

                // (Pond) Try to match these two nodes
                // should return a vector of pattern when matching PatEnode to Enode
                ematchCheckEnodeAndChildren(
                    &st,
                    eg,
                    &patternEnode,
                    patternChildren,
                    &mut out,
                    &enode,
                );
            }
            let ret = out;
            if ret.len() > 0 {
                debug!("At return, Search {} in {:?}", pattern, i);
                debug!("ret {:?}", ret);
            }
            ret
        }
        Pattern::Subst(..) => panic!(),
        Pattern::Star(_) => {
            panic!(
                "(Pond) This case should not be reached, all star should be handled like a new var"
            );
        }
    }
}

//(Pond) try to match this Pattern at this Eclass
fn matchEclassWithEveryState<L: Language, N: Analysis<L>>(
    acc: Vec<State>,
    eclassId: &AppliedId,
    childPattern: &Pattern<L>,
    eg: &EGraph<L, N>,
) -> Vec<State> {
    let mut next = Vec::new();

    let callLen = acc.len();
    let mut accIter = acc.clone().into_iter();
    debug!("matchEnode");
    debug!("eclassId {:?}", eclassId);
    debug!("childPattern {} or {:?}", childPattern, childPattern);
    for _ in 0..callLen {
        let result =
            ematchAllInEclassInternal(childPattern, accIter.next().unwrap(), eclassId.clone(), eg);
        next.extend(result);
    }

    next
}

// Try to match an Enode n with a substitue version of another Enode nn
fn ematchCheckEnodeAndChildren<L: Language, N: Analysis<L>>(
    st: &State,
    eg: &EGraph<L, N>,
    patternEnode: &L,
    patternChildren: &[Pattern<L>],
    out: &mut Vec<State>,
    eclassEnode: &L,
) {
    // debug!("eclassEnode {:?}", eclassEnode);
    // debug!("patternEnode {:?}", patternEnode);
    'nodeloop: for enode_shape in eg.get_group_compatible_weak_variants(&eclassEnode) {
        // debug!("eclassEnodeShape {:?}", enode_shape);
        if CHECKS {
            assert_eq!(&nullify_app_ids(patternEnode), patternEnode);
        }

        let clear_n2 = nullify_app_ids(&enode_shape);
        let (n_sh, _) = patternEnode.weak_shape();
        let (clear_n2_sh, _) = clear_n2.weak_shape();

        let matchWithStar =
            checkChildrenTypeEq(&n_sh.getChildrenType(), &clear_n2_sh.getChildrenType());

        if n_sh != clear_n2_sh && !matchWithStar {
            debug!("continue at shape diff {n_sh:?} != {clear_n2_sh:?}");
            continue 'nodeloop;
        }

        let mut st: State = st.clone();

        // debug!("eclassEnode slot {:?}", clear_n2.all_slot_occurrences());
        // debug!(
        //     "patternEnode slot {:?}",
        //     patternEnode.all_slot_occurrences()
        // );
        // debug!("state before try_insert, {:?}", st.partial_slotmap);
        for (x, y) in clear_n2
            .all_slot_occurrences()
            .into_iter()
            .zip(patternEnode.all_slot_occurrences().into_iter())
        {
            // (Pond) if cannot try map between pattern and enode slots
            if !try_insert_compatible_slotmap_bij(x, y, &mut st.partial_slotmap) {
                debug!("continue at !try_insert_compatible_slotmap_bij");
                continue 'nodeloop;
            }
        }
        // debug!("state after try_insert, {:?}", st.partial_slotmap);

        let mut acc = vec![st.clone()];
        let eclassChildren = enode_shape.applied_id_occurrences();
        debug!("matchChildren");
        debug!("patternChildren {:?}", patternChildren);
        debug!("eclassChildren {:?}", eclassChildren);
        for i in 0..patternChildren.len() {
            if let Pattern::Star(n) = patternChildren[i] {
                let mut counter = 0;
                assert!(i == patternChildren.len() - 1);
                let mut j = i;
                while j < eclassChildren.len() {
                    let newPVar = Pattern::PVar(format!("star_{}_{}", n, counter));
                    (acc) = matchEclassWithEveryState(acc, eclassChildren[j], &newPVar, eg);

                    j += 1;
                    counter += 1;
                }

                break;
            }

            let subId = eclassChildren[i];
            let subPat = &patternChildren[i];
            (acc) = matchEclassWithEveryState(acc, subId, subPat, eg);
        }

        debug!("matchChildren Result");
        debug!("patternChildren");
        for (i, p) in patternChildren.iter().enumerate() {
            debug!("\t {}) {}", i, p);
        }
        debug!("eclassChildren");
        for (i, e) in eclassChildren.iter().enumerate() {
            debug!("\t {}) {}", i, e);
        }
        debug!("acc {:#?}", acc);
        out.extend(acc);
    }
}

pub(crate) fn nullify_app_ids<L: Language>(l: &L) -> L {
    let mut l = l.clone();
    for x in l.applied_id_occurrences_mut() {
        *x = AppliedId::null();
    }
    l
}

fn try_insert_compatible_slotmap_bij(k: Slot, v: Slot, map: &mut SlotMap) -> bool {
    if let Some(v_old) = map.get(k) {
        if v_old != v {
            return false;
        }
    }
    map.insert(k, v);
    map.is_bijection()
}

fn final_subst(s: State) -> Subst {
    let State {
        partial_subst: mut subst,
        partial_slotmap: mut slotmap,
    } = s;

    // Previously, the subst uses `egraph`-based slot names.
    // Afterwards, the subst uses `pattern`-based slot names.
    for (_, v) in subst.iter_mut() {
        // All slots that are not covered by the pattern, need a fresh new name.
        for s in v.slots() {
            if !slotmap.contains_key(s) {
                slotmap.insert(s, Slot::fresh());
            }
        }

        *v = v.apply_slotmap(&slotmap);
    }

    subst
}
