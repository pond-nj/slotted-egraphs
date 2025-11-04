use core::panic;

use crate::*;
use log::debug;

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
/// A Pattern to match against, or as the rhs of a rewrite rule.
///
/// - It supports pattern-variables `?x` to match against anything.
/// - It supports (on the rhs) substitutions `b[x := t]` to substitute natively.
pub enum Pattern<L: Language> {
    ENode(L, Vec<Pattern<L>>),
    PVar(String),                                             // ?x
    Star(u32),                                                // *
    Subst(Box<Pattern<L>>, Box<Pattern<L>>, Box<Pattern<L>>), // Subst(b, x, t) means `b[x := t]`
}

pub fn replaceStarInPatternFromSubst<L: Language>(pattern: &mut Pattern<L>, subst: &Subst) {
    if let Pattern::ENode(enode, children) = pattern {
        for (i, child) in children.iter_mut().enumerate() {
            match child {
                Pattern::ENode(..) => replaceStarInPatternFromSubst(child, subst),
                Pattern::Star(_) => {
                    assert!(i == children.len() - 1);
                    break;
                }
                _ => {}
            }
        }

        let mut n: Option<u32> = None;
        {
            if let Some(Pattern::Star(nth)) = children.last() {
                n = Some(*nth);
            }
        }

        // TODO(Pond): now only suppost one vector as a children
        if let Some(n) = n {
            let mut counter = 0;
            children.pop();
            enode.shrinkChildren();
            while subst.contains_key(&format!("star_{}_{}", n, counter)) {
                children.push(Pattern::PVar(format!("star_{}_{}", n, counter)));
                enode.expandChildren();
                counter += 1;
            }
        }

        return;
    }
}

pub fn constructENodefromPatternSubstInternal<L: Language, N: Analysis<L>>(
    eg: &EGraph<L, N>,
    pattern: &Pattern<L>,
    subst: &Subst,
) -> Option<(AppliedId, Option<L>)> {
    match &pattern {
        Pattern::ENode(n, children) => {
            let mut n = n.clone();
            let mut refs = n.applied_id_occurrences_mut();
            if CHECKS {
                assert_eq!(children.len(), refs.len());
            }
            // (Pond): Recursively updat children pointer
            for i in 0..refs.len() {
                let Some((childAppId, _)) =
                    constructENodefromPatternSubstInternal(eg, &children[i], subst)
                else {
                    return None;
                };
                *(refs[i]) = childAppId;
            }
            let Some(resAppId) = eg.lookup(&n) else {
                return None;
            };
            Some((resAppId, Some(n)))
        }
        Pattern::PVar(v) => Some((
            subst
                .get(v)
                .unwrap_or_else(|| {
                    panic!("encountered `?{v}` in pattern, but it is missing in the `subst`")
                })
                .clone(),
            None,
        )),
        Pattern::Subst(..) | Pattern::Star(_) => {
            panic!()
        }
    }
}

pub fn constructENodefromPatternSubst<L: Language, N: Analysis<L>>(
    eg: &EGraph<L, N>,
    pattern: &Pattern<L>,
    subst: &Subst,
) -> Option<L> {
    let pattern = &mut pattern.clone();
    replaceStarInPatternFromSubst(pattern, subst);

    let Some((_appId, someNode)) = constructENodefromPatternSubstInternal(eg, pattern, subst)
    else {
        return None;
    };

    // if return something, the node must exists
    Some(someNode.unwrap())
}

fn pattern_substInternal<L: Language, N: Analysis<L>>(
    eg: &mut EGraph<L, N>,
    pattern: &Pattern<L>,
    subst: &Subst,
) -> AppliedId {
    match &pattern {
        Pattern::ENode(n, children) => {
            let mut n = n.clone();
            let mut refs = n.applied_id_occurrences_mut();
            if CHECKS {
                assert_eq!(children.len(), refs.len());
            }
            // (Pond): Recursively update children pointer
            for i in 0..refs.len() {
                *(refs[i]) = pattern_substInternal(eg, &children[i], subst);
            }
            eg.add_syn(n)
        }
        Pattern::PVar(v) => subst
            .get(v)
            .unwrap_or_else(|| {
                panic!("encountered `?{v}` in pattern, but it is missing in the `subst`")
            })
            .clone(),
        Pattern::Subst(b, x, t) => {
            let b = pattern_substInternal(eg, &*b, subst);
            let x = pattern_substInternal(eg, &*x, subst);
            let t = pattern_substInternal(eg, &*t, subst);

            // temporary swap-out so that we can access both the e-graph and the subst-method fully.
            let mut method = eg.subst_method.take().unwrap();
            let out = method.subst(b, x, t, eg);
            eg.subst_method = Some(method);
            out
        }
        Pattern::Star(_) => {
            panic!()
        }
    }
}

// Subst variable in the pattern and add the pattern to Egraph
// We write this as pattern[subst] for short.
pub fn pattern_subst<L: Language, N: Analysis<L>>(
    eg: &mut EGraph<L, N>,
    pattern: &Pattern<L>,
    subst: &Subst,
) -> AppliedId {
    let pattern = &mut pattern.clone();
    replaceStarInPatternFromSubst(pattern, subst);

    debug!("calling pattern_substInternal on {pattern:#?}");
    // debug!("with {subst:#?}");
    pattern_substInternal(eg, &pattern, subst)
}

pub fn patternSubstStr<L: Language, N: Analysis<L>>(
    eg: &mut EGraph<L, N>,
    patternStr: &str,
    subst: &Subst,
) -> AppliedId {
    let mut pattern = Pattern::parse(patternStr).unwrap();
    replaceStarInPatternFromSubst(&mut pattern, subst);
    debug!("patternStr: {patternStr:#?}");
    debug!("calling pattern_substInternal on {pattern:#?}");
    // debug!("with {subst:#?}");
    pattern_substInternal(eg, &pattern, subst)
}

// TODO maybe move into EGraph API?
pub fn lookup_rec_expr<L: Language, N: Analysis<L>>(
    re: &RecExpr<L>,
    eg: &EGraph<L, N>,
) -> Option<AppliedId> {
    let mut n = re.node.clone();
    let mut refs: Vec<&mut AppliedId> = n.applied_id_occurrences_mut();
    if CHECKS {
        assert_eq!(re.children.len(), refs.len());
    }
    for i in 0..refs.len() {
        *(refs[i]) = lookup_rec_expr(&re.children[i], eg)?;
    }
    eg.lookup(&n)
}

pub fn pattern_to_re<L: Language>(pat: &Pattern<L>) -> RecExpr<L> {
    let Pattern::ENode(n, children) = &pat else {
        panic!()
    };
    let children: Vec<RecExpr<L>> = children.iter().map(|x| pattern_to_re(x)).collect();
    RecExpr {
        node: n.clone(),
        children,
    }
}

pub fn re_to_pattern<L: Language>(re: &RecExpr<L>) -> Pattern<L> {
    let children: Vec<Pattern<L>> = re.children.iter().map(|x| re_to_pattern(x)).collect();
    Pattern::ENode(re.node.clone(), children)
}
