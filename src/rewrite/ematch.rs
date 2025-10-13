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
    let mut outPatterns = vec![];
    for i in eg.ids() {
        let i = eg.mk_sem_identity_applied_id(i);
        let result = ematchAllInEclassInternal(pattern, State::default(), i, eg);
        out.extend(result.0.into_iter().map(final_subst));
        outPatterns.extend(result.1);
    }
    debug!("ematch_all result out = {out:#?}");
    debug!("ematch_all result outPatterns = {outPatterns:#?}");
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
    out.extend(result.0.into_iter().map(final_subst));
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
) -> (Vec<State>, Vec<Pattern<L>>) {
    match &pattern {
        Pattern::PVar(v) => {
            let mut st = st;
            if let Some(j) = st.partial_subst.get(v) {
                if !eg.eq(&i, j) {
                    return (Vec::new(), Vec::new());
                }
            } else {
                st.partial_subst.insert(v.clone(), i);
            }
            (vec![st], vec![Pattern::PVar(v.to_string())])
        }
        Pattern::ENode(patternEnode, patternChildren) => {
            let mut out = Vec::new();
            let mut outPatternChildren = vec![];
            let enodesInEclass = eg.enodes_applied(&i);
            for enode in enodesInEclass {
                // (Pond) n is from a pattern, nn is an enode.
                // (Pond) find the same type of Enode.
                let d = std::mem::discriminant(patternEnode);
                let dd = std::mem::discriminant(&enode);
                if d != dd {
                    debug!("continue because of discriminant mismatch");
                    continue;
                };

                let mut thisOut = vec![];

                // (Pond) Try to match these two nodes
                // should return a vector of pattern when matching PatEnode to Enode
                ematchCheckEnodeAndChildren(
                    &st,
                    eg,
                    &patternEnode,
                    patternChildren,
                    &mut out,
                    &enode,
                    &mut thisOut,
                );
                // assert!(out.len() == thisOut.len());

                outPatternChildren.extend(thisOut);
            }
            (out, outPatternChildren)
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
    accPatternChildren: Vec<Vec<Pattern<L>>>,
) -> (Vec<State>, Vec<Vec<Pattern<L>>>) {
    let mut next = Vec::new();
    let mut nextPatternChildren = vec![];

    let callLen = acc.len();
    let mut accIter = acc.clone().into_iter();

    for _ in 0..callLen {
        let (result, resultPatternChildren) =
            ematchAllInEclassInternal(childPattern, accIter.next().unwrap(), eclassId.clone(), eg);
        next.extend(result);
        nextPatternChildren.extend(resultPatternChildren);
    }

    // assert!(next.len() == nextPatternChildren.len()); //shouldn't hold here
    debug!("acc = {:#?}", acc);
    debug!("accPatternChildren = {accPatternChildren:#?}");
    debug!("next = {next:#?}");
    debug!("nextPatternChildren = {nextPatternChildren:#?}");

    let mut nextAccPatternChildren = vec![];
    for nextPat in nextPatternChildren {
        for tmpPatternChildren in accPatternChildren.iter() {
            let mut newTmpPatternChildren = tmpPatternChildren.clone();
            newTmpPatternChildren.push(nextPat.clone());
            nextAccPatternChildren.push(newTmpPatternChildren);
        }
    }

    debug!("nextAccPatternChildren = {:#?}", nextAccPatternChildren);
    // assert!(next.len() == nextAccPatternChildren.len());
    (next, nextAccPatternChildren)
}

// Try to match an Enode n with a substitue version of another Enode nn
fn ematchCheckEnodeAndChildren<L: Language, N: Analysis<L>>(
    st: &State,
    eg: &EGraph<L, N>,
    patternEnode: &L,
    patternChildren: &[Pattern<L>],
    out: &mut Vec<State>,
    nn: &L,
    outPatternChildren: &mut Vec<Pattern<L>>,
) {
    'nodeloop: for enode_shape in eg.get_group_compatible_weak_variants(&nn) {
        if CHECKS {
            assert_eq!(&nullify_app_ids(patternEnode), patternEnode);
        }

        let clear_n2 = nullify_app_ids(&enode_shape);
        let (n_sh, _) = patternEnode.weak_shape();
        let (clear_n2_sh, _) = clear_n2.weak_shape();

        let matchWithStar =
            checkChildrenTypeEq(&n_sh.getChildrenType(), &clear_n2_sh.getChildrenType());

        if n_sh != clear_n2_sh && !matchWithStar {
            debug!("continue at {n_sh:?} != {clear_n2_sh:?}");
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
                debug!("continue at !try_insert_compatible_slotmap_bij");
                continue 'nodeloop;
            }
        }

        let mut acc = vec![st.clone()];
        let mut accPatternChildren = vec![vec![]];
        let eclassChildren = enode_shape.applied_id_occurrences();
        for i in 0..patternChildren.len() {
            if let Pattern::Star(n) = patternChildren[i] {
                let mut counter = 0;
                assert!(i == patternChildren.len() - 1);
                let mut j = i;
                while j < eclassChildren.len() {
                    let newPVar = Pattern::PVar(format!("star_{}_{}", n, counter));
                    debug!("recurse down1");
                    (acc, accPatternChildren) = matchEclassWithEveryState(
                        acc,
                        eclassChildren[j],
                        &newPVar,
                        eg,
                        accPatternChildren,
                    );

                    j += 1;
                    counter += 1;
                }

                break;
            }

            debug!("n_sh != clear_n2_sh result = {}", n_sh != clear_n2_sh);
            debug!("n_sh childrenType = {:?}", n_sh.getChildrenType());
            debug!(
                "clear_sh childrenType = {:?}",
                clear_n2_sh.getChildrenType()
            );
            debug!(
                "matchWithStar = {}",
                checkChildrenTypeEq(&n_sh.getChildrenType(), &clear_n2_sh.getChildrenType())
            );
            debug!("patternChildren = {patternChildren:#?}");
            debug!("eclassChildren = {eclassChildren:?}");

            let subId = eclassChildren[i];
            let subPat = &patternChildren[i];
            debug!("recurse down2");
            (acc, accPatternChildren) =
                matchEclassWithEveryState(acc, subId, subPat, eg, accPatternChildren);
        }

        out.extend(acc);
        for patternChildren in accPatternChildren {
            let newPat = Pattern::ENode(patternEnode.clone(), patternChildren);
            outPatternChildren.push(newPat);
        }
    }
    debug!("out = {out:#?}");
    debug!("outPatternChildren = {outPatternChildren:#?}");
    // assert!(out.len() == outPatternChildren.len());
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
