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

pub fn ematch_all<L: Language, N: Analysis<L>>(
    eg: &EGraph<L, N>,
    pattern: &Pattern<L>,
) -> Vec<Subst> {
    debug!("=== Call EmatchAll ===");
    debug!("pattern = {pattern:#?}");
    let mut out = Vec::new();
    // TODO(Pond): this will start matching at every id, which is not efficient.
    let mut counter: usize = 0;
    let mut updatedPatterns = vec![];
    for i in eg.ids() {
        let i = eg.mk_sem_identity_applied_id(i);
        let mut newUpdatedPatterns = vec![];
        out.extend(
            ematch_impl(
                pattern,
                State::default(),
                i,
                eg,
                &mut counter,
                &mut newUpdatedPatterns,
            )
            .into_iter()
            .map(final_subst),
        );
        updatedPatterns.extend(newUpdatedPatterns);
    }
    debug!("ematch_all {eg:#?}");
    debug!("ematch_all {pattern:#?}");
    debug!("ematch_all result out = {out:#?}");
    debug!("ematch_all result updatedPatterns = {updatedPatterns:#?}");
    assert!(out.len() == updatedPatterns.len());
    out
}

// (Pond) deal with Pattern cases and find Enode with same type
// `i` uses egraph slots instead of pattern slots.
// (Pond) Find pattern of that type in the eclass
fn ematch_impl<L: Language, N: Analysis<L>>(
    pattern: &Pattern<L>,
    st: State,
    i: AppliedId,
    eg: &EGraph<L, N>,
    counter: &mut usize,
    updatedPatterns: &mut Vec<Pattern<L>>,
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
                debug!("st before insert = {st:#?}");
                st.partial_subst.insert(v.clone(), i);
                debug!("st after insert = {st:#?}");
            }
            *updatedPatterns = vec![pattern.clone()];
            vec![st]
        }
        Pattern::ENode(patternEnode, children) => {
            let mut out = Vec::new();
            let enodesInEclass = eg.enodes_applied(&i);
            debug!("enodes in eclass = {enodesInEclass:?}");
            updatedPatterns.clear();
            for enode in enodesInEclass {
                // (Pond) n is from a pattern, nn is an enode.
                // (Pond) find the same type of Enode.
                let d = std::mem::discriminant(patternEnode);
                let dd = std::mem::discriminant(&enode);
                if d != dd {
                    debug!("continue because of discriminant mismatch");
                    continue;
                };

                let mut newUpdatedPatterns = vec![];

                let mut newCount = out.len();
                ematch_node(
                    &st,
                    eg,
                    &patternEnode,
                    children,
                    &mut out,
                    &enode,
                    counter,
                    &mut newUpdatedPatterns,
                );
                newCount = out.len() - newCount;
                assert!(
                    newCount == newUpdatedPatterns.len(),
                    "newCount = {newCount}, newUpdatedPatterns.len() = {}",
                    newUpdatedPatterns.len()
                );

                updatedPatterns.extend(newUpdatedPatterns);
            }
            debug!("out = {out:#?}");
            debug!("updatedPatterns = {updatedPatterns:#?}");
            assert!(out.len() == updatedPatterns.len());
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

//(Pond) try to match this Pattern at this Eclass
fn recurseDownChildrenEclass<L: Language, N: Analysis<L>>(
    acc: Vec<State>,
    sub_id: &AppliedId,
    sub_pat: &Pattern<L>,
    eg: &EGraph<L, N>,
    counter: &mut usize,
    accPatternChildren: Vec<Vec<Pattern<L>>>,
) -> (Vec<State>, Vec<Vec<Pattern<L>>>) {
    let mut next = Vec::new();
    let mut nextPatternChildren = vec![];
    let mut updatedPatterns = vec![];
    for a in acc.into_iter() {
        // (Pond) Recurse down, try to match children from pattern with AppliedIds from enode
        // TODO(Pond): This should return all updatedPatterns
        let mut newUpdatedPatterns = vec![];
        next.extend(ematch_impl(
            sub_pat,
            a,
            sub_id.clone(),
            eg,
            counter,
            &mut newUpdatedPatterns,
        ));

        updatedPatterns.extend(newUpdatedPatterns);
    }

    assert!(next.len() == updatedPatterns.len());
    for patternChildren in accPatternChildren {
        for newPattern in updatedPatterns.iter() {
            let mut newPatternChildren = patternChildren.clone();
            newPatternChildren.push(newPattern.clone());
            nextPatternChildren.push(newPatternChildren);
        }
    }

    debug!("next = {next:#?}");
    debug!("nextPatternChildren = {nextPatternChildren:#?}");
    debug!("updatedPatterns = {updatedPatterns:#?}");
    assert!(next.len() == nextPatternChildren.len());
    (next, nextPatternChildren)
}

// Try to match an Enode n with a substitue version of another Enode nn
fn ematch_node<L: Language, N: Analysis<L>>(
    st: &State,
    eg: &EGraph<L, N>,
    patternEnode: &L,
    patternChildren: &[Pattern<L>],
    out: &mut Vec<State>,
    nn: &L,
    counter: &mut usize,
    updatedPatterns: &mut Vec<Pattern<L>>,
) {
    updatedPatterns.clear();
    // (Pond) for each enode shaped differently from children eclass different permutation
    'nodeloop: for enode_shape in eg.get_group_compatible_weak_variants(&nn) {
        if CHECKS {
            assert_eq!(&nullify_app_ids(patternEnode), patternEnode);
        }

        let clear_n2 = nullify_app_ids(&enode_shape);
        // We can use weak_shape here, as the inputs are nullified
        // i.e. they only have id0() without slot args, so there are no permutations possible.
        let (n_sh, _) = patternEnode.weak_shape();
        let (clear_n2_sh, _) = clear_n2.weak_shape();
        // (Pond) they check numbers of slots here?

        let match_with_star = vec_language_children_type_eq_with_star(
            &n_sh.getChildrenType(),
            &clear_n2_sh.getChildrenType(),
        );

        debug!("match_with_star = {match_with_star:?}");

        if n_sh != clear_n2_sh && !match_with_star {
            debug!("ematch_node continue at {n_sh:?} != {clear_n2_sh:?}");
            continue 'nodeloop;
        }

        let mut st = st.clone();

        for (x, y) in clear_n2
            .all_slot_occurrences()
            .into_iter()
            .zip(patternEnode.all_slot_occurrences().into_iter())
        {
            // (Pond) if cannot try map between pattern and enode slots
            if !try_insert_compatible_slotmap_bij(x, y, &mut st.partial_slotmap) {
                debug!("ematch_node continue at !try_insert_compatible_slotmap_bij");
                continue 'nodeloop;
            }
        }

        debug!("updated partial_slotmap = {:?}", st.partial_slotmap);

        let mut acc = vec![st.clone()];
        let eclassChildren = enode_shape.applied_id_occurrences();

        let mut accPatternChildren: Vec<Vec<Pattern<L>>> = vec![vec![]];
        for i in 0..patternChildren.len() {
            if patternChildren[i] == Pattern::Star {
                assert!(i == patternChildren.len() - 1);
                let mut j = i;
                while j < eclassChildren.len() {
                    let newPVar = Pattern::PVar(format!("star_{}", counter));
                    debug!("recurse down1");
                    (acc, accPatternChildren) = recurseDownChildrenEclass(
                        acc,
                        eclassChildren[j],
                        &newPVar,
                        eg,
                        counter,
                        accPatternChildren,
                    );

                    debug!("acc return1 = {acc:#?}");
                    j += 1;
                    *counter += 1;
                }

                break;
            }

            debug!(
                "ematch_node children_type {:#?} vs {:#?}",
                n_sh.getChildrenType(),
                clear_n2_sh.getChildrenType()
            );

            let subId = eclassChildren[i];
            let subPat = &patternChildren[i];
            debug!("recurse down2");
            (acc, accPatternChildren) =
                recurseDownChildrenEclass(acc, subId, subPat, eg, counter, accPatternChildren);
            debug!("acc return2 = {acc:#?}");
        }

        debug!("eclassChildren = {eclassChildren:#?}");
        debug!("originalPattern = {patternChildren:#?}");
        debug!("out before extend = {out:#?}");
        debug!("extending out with acc = {acc:#?}");
        assert!(acc.len() == accPatternChildren.len());
        for patternChildren in accPatternChildren {
            updatedPatterns.push(Pattern::ENode(patternEnode.clone(), patternChildren));
        }
        out.extend(acc);
        debug!("out after extend = {out:#?}");
        debug!("ematch_node return out = {out:#?}");
        debug!("ematch_node, updatedPatterns = {updatedPatterns:#?}");

        // assert!(out.len() == updatedPatterns.len()); (Pond) It won't be equal because out is accumulated over every Enode in the same Eclass
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
