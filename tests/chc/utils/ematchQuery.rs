use super::*;
use log::{debug, trace};

pub fn ematchQueryall(eg: &CHCEGraph, pattern: &Pattern<CHC>) -> Vec<(Subst, Id)> {
    debug!("=== Call ematchQueryall ===");
    debug!("pattern = {pattern}");
    let mut out: Vec<(Subst, Id)> = Vec::new();
    for i in eg.ids() {
        let appId = eg.mk_sem_identity_applied_id(i);
        let result = ematchQueryAllInEclassInternal(pattern, State::default(), appId, eg);
        if result.len() > 0 {
            debug!("some match in eclass {i:?} for pattern {pattern}");
        } else {
            debug!("no match in eclass {i:?} for pattern {pattern}");
        }

        out.extend(result.into_iter().map(final_subst).map(|x| (x, i)));
    }
    out
}

fn ematchQueryAllInEclassInternal(
    pattern: &Pattern<CHC>,
    st: State,
    i: AppliedId,
    eg: &CHCEGraph,
) -> Vec<State> {
    assert!(false);
    trace!("try match in eclass {i:?} with pattern {pattern}");
    match &pattern {
        Pattern::PVar(v) => {
            let mut st = st;
            if let Some(j) = st.partial_subst.get(v) {
                if !eg.eq(&i, j) {
                    debug!("check existing var {j:?} vs new var {i:?}, fail");
                    return Vec::new();
                } else {
                    // debug!("check existing var {:?}, pass", i);
                }
            } else {
                debug!("insert partial_subst {v:?} -> {i:?}");
                st.partial_subst.insert(v.clone(), i.clone());
            }
            let ret = vec![st];
            ret
        }
        Pattern::ENode(patternEnode, patternChildren) => {
            let mut out = Vec::new();
            let enodesInEclass = eg.enodes_applied(&i);
            for (enodeIdx, enode) in enodesInEclass.into_iter().enumerate() {
                // (Pond) n is from a pattern, nn is an enode.
                // (Pond) find the same type of Enode.
                let d = std::mem::discriminant(patternEnode);
                let dd = std::mem::discriminant(&enode);
                if d != dd {
                    // debug!("continue because of discriminant mismatch");
                    continue;
                };

                debug!("try {enodeIdx}th enode in {i}, {enode:?}");

                // (Pond) Try to match these two nodes
                // should return a vector of pattern when matching PatEnode to Enode
                let outLenBefore = out.len();

                ematchQueryCheckEnodeAndChildren(
                    &st,
                    eg,
                    &patternEnode,
                    patternChildren,
                    &mut out,
                    &enode,
                );

                if out.len() - outLenBefore > 0 {
                    debug!("{enodeIdx}th enode found matched");
                } else {
                    debug!("{enodeIdx}th enode not found matched");
                }
            }
            let ret = out;
            if ret.len() > 0 {
                // debug!("At return, Search {} in {:?}", pattern, i);
                // debug!("ret {:?}", ret);
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

fn matchQueryEclassWithEveryState(
    acc: Vec<State>,
    eclassId: &AppliedId,
    childPattern: &Pattern<CHC>,
    eg: &CHCEGraph,
) -> Vec<State> {
    let mut next = Vec::new();

    let callLen = acc.len();
    let mut accIter = acc.clone().into_iter();
    // debug!("matchEnode with acc {:#?}", acc);
    // debug!("eclassId {:?}", eclassId);
    // debug!("childPattern {} or {:?}", childPattern, childPattern);
    for _ in 0..callLen {
        let result = ematchQueryAllInEclassInternal(
            childPattern,
            accIter.next().unwrap(),
            eclassId.clone(),
            eg,
        );
        next.extend(result);
    }

    next
}

fn ematchQueryCheckEnodeAndChildren(
    st: &State,
    eg: &CHCEGraph,
    patternEnode: &CHC,
    patternChildren: &[Pattern<CHC>],
    out: &mut Vec<State>,
    eclassEnode: &CHC,
) {
    let mut allSetOfChildren = vec![];
    match patternEnode {
        CHC::And(_) | CHC::Compose(_) => {
            let childrenPermute = permute_iter(&patternChildren);

            if childrenPermute.len() == 0 {
                allSetOfChildren.push(patternChildren.to_vec());
            }

            allSetOfChildren.extend(childrenPermute);
        }
        CHC::New(..) => {
            let childrenPermute = permute_iter(&patternChildren[2..]);

            if childrenPermute.len() == 0 {
                allSetOfChildren.push(patternChildren.to_vec());
            }

            for ithPermute in childrenPermute {
                let mut newPatternChildren =
                    vec![patternChildren[0].clone(), patternChildren[1].clone()];
                newPatternChildren.extend(ithPermute);
                allSetOfChildren.push(newPatternChildren);
            }
        }
        CHC::Eq(..) => {
            assert!(patternChildren.len() == 2);
            allSetOfChildren.push(patternChildren.to_vec());
            allSetOfChildren
                .push([patternChildren[1].clone(), patternChildren[0].clone()].to_vec());
        }
        _ => {
            allSetOfChildren.push(patternChildren.to_vec());
        }
    }

    let outLenBefore = out.len();

    assert!(allSetOfChildren.len() > 0);
    for patternChildren in allSetOfChildren {
        debug!(
            "try match to {eclassEnode:?} with patEnode {patternEnode:?} and {patternChildren:?}"
        );
        let enodes = eg.get_group_compatible_weak_variants(&eclassEnode);
        assert!(!enodes.is_empty());
        'nodeloop: for enode_shape in enodes {
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

            for (x, y) in clear_n2
                .all_slot_occurrences()
                .into_iter()
                .zip(patternEnode.all_slot_occurrences().into_iter())
            {
                // (Pond) if cannot try map between pattern and enode slots
                if !try_insert_compatible_slotmap_bij(x, y, &mut st.partial_slotmap) {
                    debug!("continue at !try_insert_compatible_slotmap_bij");
                    debug!("cannot insert {x:?} -> {y:?} in {st:?}");
                    continue 'nodeloop;
                } else {
                    debug!("insert partial_slotmap {x:?} -> {y:?}");
                }
            }

            let mut acc = vec![st.clone()];
            let eclassChildren = enode_shape.applied_id_occurrences();

            debug!("shape pass, try to match children");

            let mut starCount = 0;
            for i in 0..patternChildren.len() {
                if let Pattern::Star(_) = patternChildren[i] {
                    starCount += 1;
                }
            }
            assert!(starCount <= 1);

            let mut countNonStarFromBack = 0;
            for i in (0..patternChildren.len()).rev() {
                if let Pattern::Star(_) = patternChildren[i] {
                    break;
                }
                countNonStarFromBack += 1;
            }

            // forward match
            let mut i = 0;
            let mut j = 0;
            while i < patternChildren.len() && j < eclassChildren.len() {
                if let Pattern::Star(n) = patternChildren[i] {
                    let mut counter = 0;
                    while j < eclassChildren.len() - countNonStarFromBack {
                        let newPVar = Pattern::PVar(format!("star_{}_{}", n, counter));
                        (acc) =
                            matchQueryEclassWithEveryState(acc, eclassChildren[j], &newPVar, eg);
                        // debug!("acc star {acc:?}");

                        j += 1;
                        counter += 1;
                    }

                    i += 1;

                    continue;
                }

                let subPat = &patternChildren[i];
                let subId = eclassChildren[j];
                (acc) = matchQueryEclassWithEveryState(acc, subId, subPat, eg);
                i += 1;
                j += 1;
            }
            if patternChildren.len() > eclassChildren.len() {
                assert!(i == patternChildren.len() - 1 || i == patternChildren.len());
                assert!(j == eclassChildren.len());
            } else {
                assert!(i == patternChildren.len());
                assert!(j == eclassChildren.len());
            }

            // backward match

            if acc.len() > 0 {
                debug!("some match found");
            } else {
                debug!("no match found");
            }

            // debug!("matchChildren Result");
            // debug!("patternChildren");
            // for (i, p) in patternChildren.iter().enumerate() {
            //     debug!("\t {}) {}", i, p);
            // }
            // debug!("eclassChildren");
            // for (i, e) in eclassChildren.iter().enumerate() {
            //     debug!("\t {}) {}", i, e);
            // }
            // debug!("acc {:#?}", acc);
            out.extend(acc);
        }

        // TODO: this rule-out some matches that we need, why?
        // if out.len() > outLenBefore {
        //     break;
        // }
    }

    // patternEnode: &CHC,
    // patternChildren: &[Pattern<CHC>],
    // eclassEnode: &CHC,
    debug!("return {} try match to {eclassEnode:?} with patEnode {patternEnode:?} and {patternChildren:?}", out.len() - outLenBefore);
}
