use crate::*;
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

#[logfn(debug)]
#[logfn_inputs(debug)]
pub fn ematch_all<L: Language, N: Analysis<L>>(
    eg: &EGraph<L, N>,
    pattern: &Pattern<L>,
) -> Vec<Subst> {
    let mut out = Vec::new();
    // TODO(Pond): this will start matching at every id, which is not efficient.
    let mut counter: usize = 0;
    for i in eg.ids() {
        let i = eg.mk_sem_identity_applied_id(i);
        out.extend(
            ematch_impl(pattern, State::default(), i, eg, &mut counter)
                .into_iter()
                .map(final_subst),
        );
    }
    debug!("ematch_all {eg:#?}");
    debug!("ematch_all {pattern:#?}");
    out
}

// (Pond) deal with Pattern cases and find Enode with same type
// `i` uses egraph slots instead of pattern slots.
#[logfn(debug)]
#[logfn_inputs(debug)]
fn ematch_impl<L: Language, N: Analysis<L>>(
    pattern: &Pattern<L>,
    st: State,
    i: AppliedId,
    eg: &EGraph<L, N>,
    counter: &mut usize,
) -> Vec<State> {
    match &pattern {
        Pattern::PVar(v) => {
            let mut st = st;
            if let Some(j) = st.partial_subst.get(v) {
                if !eg.eq(&i, j) {
                    return Vec::new();
                }
            } else {
                // (Pond) why does this insert a mapping from v to AppliedId? Is AppliedId representative of one Eclass
                // (Pond) Don't one Eclass has many version of AppliedId?, Do we only need to insert one mapping?
                println!("st before insert = {st:#?}");
                st.partial_subst.insert(v.clone(), i);
                println!("st after insert = {st:#?}");
            }
            vec![st]
        }
        Pattern::ENode(n, children) => {
            let mut out = Vec::new();
            let enodes = eg.enodes_applied(&i);
            debug!("ematch_impl enodes in eclass = {enodes:?}");
            for nn in enodes {
                // (Pond) n is from a pattern, nn is an enode.
                // (Pond) find the same type of Enode.
                let d = std::mem::discriminant(n);
                let dd = std::mem::discriminant(&nn);
                if d != dd {
                    debug!("ematch_impl continue at {d:?} != {dd:?}");
                    continue;
                };

                ematch_node(&st, eg, &n, children, &mut out, &nn, counter);
            }
            debug!("ematch_impl, ENode case out = {out:#?}");
            out
        }
        Pattern::Subst(..) => panic!(),
        Pattern::Star => {
            panic!(
                "(Pond) This case should not be reached, all star should be handled like a new var"
            );
        }
    }
}

fn recurse_down_children_eclass<L: Language, N: Analysis<L>>(
    acc: Vec<State>,
    sub_id: &AppliedId,
    sub_pat: &Pattern<L>,
    eg: &EGraph<L, N>,
    counter: &mut usize,
) -> Vec<State> {
    let mut next = Vec::new();
    for a in acc.into_iter() {
        // (Pond) Recurse down, try to match children from pattern with AppliedIds from enode
        debug!("recursing down with ematch_impl with sub_pat = {sub_pat:?}, a = {a:?}, sub_id = {sub_id:?}");
        next.extend(ematch_impl(sub_pat, a, sub_id.clone(), eg, counter));
    }
    next
}

// Try to match an Enode n with a substitue version of another Enode nn
fn ematch_node<L: Language, N: Analysis<L>>(
    st: &State,
    eg: &EGraph<L, N>,
    n: &L,
    children: &[Pattern<L>],
    out: &mut Vec<State>,
    nn: &L,
    counter: &mut usize,
) {
    // (Pond) for each enode shaped differently from children eclass different permutation
    'nodeloop: for enode_shape in eg.get_group_compatible_weak_variants(&nn) {
        if CHECKS {
            assert_eq!(&nullify_app_ids(n), n);
        }

        let clear_n2 = nullify_app_ids(&enode_shape);
        // We can use weak_shape here, as the inputs are nullified
        // i.e. they only have id0() without slot args, so there are no permutations possible.
        let (n_sh, _) = n.weak_shape();
        let (clear_n2_sh, _) = clear_n2.weak_shape();
        // (Pond) they check numbers of slots here?
        debug!(
            "ematch_node children_type {:?} vs {:?}",
            n_sh.get_children_type(),
            clear_n2_sh.get_children_type()
        );

        println!("ematch_node before n_sh = {n_sh:?}");
        println!("ematch_node before clear_n2_sh = {clear_n2_sh:?}");
        let match_with_star = vec_language_children_type_eq_with_star(
            &n_sh.get_children_type(),
            &clear_n2_sh.get_children_type(),
        );
        println!("ematch_node after n_sh = {n_sh:?}");
        println!("ematch_node after clear_n2_sh = {clear_n2_sh:?}");
        // debug!("ematch_node match_with_star = {match_with_star}");

        // if n_sh != clear_n2_sh && !match_with_star {
        //     debug!("ematch_node continue at {n_sh:?} != {clear_n2_sh:?}");
        //     continue 'nodeloop;
        // }

        if n_sh != clear_n2_sh {
            debug!("ematch_node continue at {n_sh:?} != {clear_n2_sh:?}");
            continue 'nodeloop;
        }

        let mut st = st.clone();

        for (x, y) in clear_n2
            .all_slot_occurrences()
            .into_iter()
            .zip(n.all_slot_occurrences().into_iter())
        {
            // (Pond) if cannot try map between pattern and enode slots
            debug!("try map slot x = {:?}, y = {:?}", x, y);
            if !try_insert_compatible_slotmap_bij(x, y, &mut st.partial_slotmap) {
                debug!("ematch_node continue at !try_insert_compatible_slotmap_bij");
                continue 'nodeloop;
            }
        }

        debug!("updated partial_slotmap = {:?}", st.partial_slotmap);

        let mut acc = vec![st];

        // (Pond) enode_shape.applied_id_occurrences() = list of AppliedIds (children Eclasses) from enode
        let eclass_children = enode_shape.applied_id_occurrences();

        if eclass_children.len() != children.len() {
            assert!(children.last().unwrap() == &Pattern::Star);
            assert!(eclass_children.len() > children.len());
            for i in 0..children.len() {
                if children[i] == Pattern::Star {
                    assert!(i == children.len() - 1);
                    let mut j = i;
                    while j < eclass_children.len() {
                        // TODO(Pond) create new PVar and call the statement inside the for loop with the new PVar
                        let new_pvar = Pattern::PVar(format!("star_{}", counter));
                        acc = recurse_down_children_eclass(
                            acc,
                            eclass_children[j],
                            &new_pvar,
                            eg,
                            counter,
                        );
                        j += 1;
                        *counter += 1;
                    }
                }

                let sub_id = eclass_children[i];
                let sub_pat = &children[i];
                acc = recurse_down_children_eclass(acc, sub_id, sub_pat, eg, counter);
            }

            return;
        }

        // (Pond) children = list of Enodes children from pattern
        for (sub_id, sub_pat) in eclass_children.into_iter().zip(children.iter()) {
            acc = recurse_down_children_eclass(acc, sub_id, sub_pat, eg, counter);
        }

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
