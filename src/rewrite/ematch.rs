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
    let mut outPatterns = vec![];
    for i in eg.ids() {
        let i = eg.mk_sem_identity_applied_id(i);
        let result = ematch_impl(pattern, State::default(), i, eg, &mut counter, vec![]);
        out.extend(result.0.into_iter().map(final_subst));
        outPatterns.extend(result.1);
    }
    debug!("ematch_all result out = {out:#?}");
    debug!("ematch_all result outPatterns = {outPatterns:#?}");
    assert!(out.len() == outPatterns.len());
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
    mut tmpPatternChildren: Vec<Pattern<L>>,
) -> (Vec<State>, Vec<Vec<Pattern<L>>>) {
    match &pattern {
        Pattern::PVar(v) => {
            let mut st = st;
            if let Some(j) = st.partial_subst.get(v) {
                if !eg.eq(&i, j) {
                    return (Vec::new(), Vec::new());
                }
            } else {
                // (Pond) why does this insert a mapping from v to AppliedId? Is AppliedId representative of one Eclass
                // (Pond) Don't one Eclass has many version of AppliedId?, Do we only need to insert one mapping?
                debug!("st before insert = {st:#?}");
                st.partial_subst.insert(v.clone(), i);
                debug!("st after insert = {st:#?}");
            }
            tmpPatternChildren.push(Pattern::PVar(v.to_string()));
            (vec![st], vec![tmpPatternChildren])
        }
        Pattern::ENode(patternEnode, patternChildren) => {
            let mut out = Vec::new();
            let mut outPatternChildren = vec![];
            let enodesInEclass = eg.enodes_applied(&i);
            debug!("enodes in eclass = {enodesInEclass:?}");
            for enode in enodesInEclass {
                // (Pond) n is from a pattern, nn is an enode.
                // (Pond) find the same type of Enode.
                let d = std::mem::discriminant(patternEnode);
                let dd = std::mem::discriminant(&enode);
                if d != dd {
                    debug!("continue because of discriminant mismatch");
                    continue;
                };

                // (Pond) Try to match these two nodes
                ematch_node(
                    &st,
                    eg,
                    &patternEnode,
                    patternChildren,
                    &mut out,
                    &enode,
                    counter,
                    tmpPatternChildren.clone(),
                    &mut outPatternChildren,
                );
                assert!(out.len() == outPatternChildren.len());
            }
            (out, outPatternChildren)
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
    assert!(acc.len() == accPatternChildren.len());
    let callLen = acc.len();
    let mut accIter = acc.into_iter();
    let mut accPatternChildrenIter = accPatternChildren.into_iter();
    for _ in 0..callLen {
        // (Pond) Recurse down, try to match this pattern at this Eclass
        // TODO(Pond): This should return all updatedPatterns
        let (result, resultPatternChildren) = ematch_impl(
            sub_pat,
            accIter.next().unwrap(),
            sub_id.clone(),
            eg,
            counter,
            accPatternChildrenIter.next().unwrap(),
        );
        next.extend(result);
        nextPatternChildren.extend(resultPatternChildren);
    }

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
    tmpPatternChildren: Vec<Pattern<L>>,
    outPatternChildren: &mut Vec<Vec<Pattern<L>>>,
) {
    // (Pond) for each enode shaped differently from children eclass different permutation
    'nodeloop: for enode_shape in eg.get_group_compatible_weak_variants(&nn) {
        if CHECKS {
            assert_eq!(&nullify_app_ids(patternEnode), patternEnode);
        }

        let clear_n2 = nullify_app_ids(&enode_shape);
        let (n_sh, _) = patternEnode.weak_shape();
        let (clear_n2_sh, _) = clear_n2.weak_shape();
        // (Pond) they check numbers of slots here?

        let matchWithStar =
            checkChildrenTypeEq(&n_sh.getChildrenType(), &clear_n2_sh.getChildrenType());
        debug!("matchWithStar = {matchWithStar:?}");

        if n_sh != clear_n2_sh && !matchWithStar {
            debug!("ematch_node continue at {n_sh:?} != {clear_n2_sh:?}");
            continue 'nodeloop;
        }

        let mut st: State = st.clone();

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

        let mut acc = vec![st.clone()];
        let mut accPatternChildren = vec![tmpPatternChildren.clone()];
        let eclassChildren = enode_shape.applied_id_occurrences();

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

            let subId = eclassChildren[i];
            let subPat = &patternChildren[i];
            debug!("recurse down2");
            (acc, accPatternChildren) =
                recurseDownChildrenEclass(acc, subId, subPat, eg, counter, accPatternChildren);
            debug!("acc return2 = {acc:#?}");
        }

        assert!(acc.len() == accPatternChildren.len());
        out.extend(acc);
        outPatternChildren.extend(accPatternChildren);
        assert!(out.len() == outPatternChildren.len());
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
