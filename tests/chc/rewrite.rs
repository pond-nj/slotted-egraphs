use super::*;
use crate::*;
use log::debug;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use union_find::{QuickUnionUf, UnionBySize, UnionFind};

static gCounter: AtomicUsize = AtomicUsize::new(0);

use std::collections::HashSet;
fn unfold() -> CHCRewrite {
    let rootPatRaw =
        Pattern::parse("(compose <(new ?syntax1 (true) <(compose <*1>) *2>) *3>)").unwrap();
    let rootPat: Rc<Pattern<CHC>> = Rc::new(rootPatRaw);
    let rootPat2 = Rc::clone(&rootPat);

    let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<Subst> { ematch_all(eg, &rootPat) });
    let applier = Box::new(
        // (compose <[(new ?syntax2 (true) <*4>) \dot (#matches of *1)] *3>)
        move |substs: Vec<Subst>, eg: &mut CHCEGraph| {
            debug!("unfold rule, found {:#?}", substs);
            for subst in substs {
                let star1Max = getMaxStarCount(1, &subst);

                let mut matches: Vec<Vec<AppliedId>> = vec![];
                // match in star1 Eclass
                for star1Count in 0..star1Max {
                    let subPat = Pattern::parse("(new ?syntax2 (true) <*4>)").unwrap();
                    let var = &starPVar(1, star1Count);
                    let result: Vec<Subst> =
                        ematchAllInEclass(eg, &subPat, subst[var].id, &subst[var].m);
                    let mut thisNewIds: Vec<AppliedId> = vec![];

                    let toPat = Pattern::parse(&format!(
                        "(new ?syntax1 (true) <{} *4>)",
                        starPStr(2, &subst)
                    ))
                    .unwrap();

                    for mut r in result {
                        mergeSubst(&mut r, &subst);
                        let newId = pattern_subst(eg, &toPat, &r);
                        thisNewIds.push(newId);
                    }
                    matches.push(thisNewIds);
                }

                let matchesCombination: Vec<Vec<AppliedId>> = combination(matches);
                let newEnode =
                    Pattern::parse(&format!("(compose <{} *4>)", starPStr(3, &subst))).unwrap();
                for m in matchesCombination {
                    // Create a new compose Enode whose children is the vector of AppliedId and union it with the original Compose
                    let mut newSubst = subst.clone();
                    let mut star4Count = 0;
                    for id in m {
                        let key = starPVar(4, star4Count);
                        assert!(!newSubst.contains_key(&key));
                        newSubst.insert(key, id);
                        star4Count += 1;
                    }

                    eg.union_instantiations(
                        &*rootPat2,
                        &newEnode,
                        &newSubst,
                        Some("Unfold".to_string()),
                    );
                }
            }
        },
    );
    RewriteT {
        searcher: searcher,
        applier: applier,
    }
    .into()
}

fn newChildrenPermute() -> CHCRewrite {
    let pat = Pattern::parse("(new ?syntax ?cond <*1>)").unwrap();
    let patClone = pat.clone();
    let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<Subst> { ematch_all(eg, &patClone) });
    let applier = Box::new(move |substs: Vec<Subst>, eg: &mut CHCEGraph| {
        // TODO: is there a different between using AppliedId and Id
        let mut did = HashSet::<(AppliedId, AppliedId, BTreeSet<AppliedId>)>::default();
        let newPat = Pattern::parse("(new ?syntax ?cond <*2>)").unwrap();
        for subst in substs {
            let mut thisDid = BTreeSet::<AppliedId>::default();
            for (var, id) in subst.iter() {
                thisDid.insert(id.clone());
            }

            let mut this = (subst["syntax"].clone(), subst["cond"].clone(), thisDid);
            if did.contains(&this) {
                continue;
            }

            did.insert(this);

            let ids = starIds(1, &subst);
            let idsPermuts = permute(&ids);
            let mut newSubst = subst.clone();
            for permut in idsPermuts {
                let mut newSubstTmp = newSubst.clone();
                for (i, id) in permut.iter().enumerate() {
                    newSubstTmp.insert(starPVar(2, i.try_into().unwrap()), id.clone());
                }
                eg.union_instantiations(
                    &pat,
                    &newPat,
                    &newSubstTmp,
                    Some("newChildrenPermute".to_string()),
                );
            }
        }
    });
    RewriteT { searcher, applier }.into()
}

// TODO: can use marking to determine that we already permute this Enode
fn composeChildrenPermute() -> CHCRewrite {
    let pat = Pattern::parse("(compose <*1>)").unwrap();
    let patClone = pat.clone();
    let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<Subst> { ematch_all(eg, &patClone) });
    let applier = Box::new(move |substs: Vec<Subst>, eg: &mut CHCEGraph| {
        // TODO: is there a different between using AppliedId and Id
        let mut did = HashSet::<BTreeSet<AppliedId>>::default();
        let newPat = Pattern::parse("(compose <*2>)").unwrap();
        for subst in substs {
            let mut thisDid = BTreeSet::<AppliedId>::default();
            for (var, id) in subst.iter() {
                thisDid.insert(id.clone());
            }

            if did.contains(&thisDid) {
                continue;
            }

            did.insert(thisDid);

            let ids = starIds(1, &subst);
            let idsPermuts = permute(&ids);
            let mut newSubst = subst.clone();
            for permut in idsPermuts {
                let mut newSubstTmp = newSubst.clone();
                for (i, id) in permut.iter().enumerate() {
                    newSubstTmp.insert(starPVar(2, i.try_into().unwrap()), id.clone());
                }
                eg.union_instantiations(
                    &pat,
                    &newPat,
                    &newSubstTmp,
                    Some("composeChildrenPermute".to_string()),
                );
            }
        }
    });
    RewriteT { searcher, applier }.into()
}

fn defineFromSharingBlock() -> CHCRewrite {
    let pat = Pattern::parse("(new ?syntax ?cond <*1>)").unwrap();
    let patClone = pat.clone();
    let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<Subst> { ematch_all(eg, &patClone) });
    let applier = Box::new(move |substs: Vec<Subst>, eg: &mut CHCEGraph| {
        debug!("define found {:?}", substs);
        for subst in substs {
            let rootAppId = pattern_subst(eg, &pat, &subst);
            debug!(
                "root eclass {:?} {:?}",
                rootAppId.id,
                eg.eclass(rootAppId.id).unwrap()
            );

            let origENode = eg
                .getExactEnodeInEGraph(&constructENodefromPatternSubst(eg, &pat, &subst).unwrap());

            // TODO: try change to rootData instead of mergeVarTypes
            let mut rootData = eg.analysis_data(rootAppId.id).varTypes.clone();
            let mut varToChildIndx: HashMap<Slot, Vec<usize>> = HashMap::default();
            let mut mergeVarTypes: HashMap<Slot, VarType> = HashMap::default();
            let childAppIds = &origENode.applied_id_occurrences()[2..];
            debug!("childAppIds {childAppIds:#?}");
            for indx in 0..childAppIds.len() {
                let appId = childAppIds[indx];
                debug!("appId.slots {:?}", appId.slots());
                for s in appId.slots() {
                    varToChildIndx.entry(s).or_insert(vec![]).push(indx);
                }

                let varTypes = &eg.analysis_data(appId.id).varTypes;
                mergeVarTypes.extend(varTypes.clone().into_iter().map(|(s, vt)| (appId.m[s], vt)));
            }

            debug!("mergeVarTypes = {mergeVarTypes:#?}");
            debug!("varToChildIndx = {varToChildIndx:#?}");

            let mut unionfind: QuickUnionUf<UnionBySize> =
                QuickUnionUf::<UnionBySize>::new(childAppIds.len());
            let mut hasNonBasicVar = vec![false; childAppIds.len()];

            for (var, childrenIndx) in &varToChildIndx {
                debug!("var = {var:?}");
                if isNonBasicVar(&mergeVarTypes[var]) {
                    let leader = childrenIndx.first().unwrap();
                    for next in childrenIndx {
                        unionfind.union(*leader, *next);
                        hasNonBasicVar[*next] = true;
                    }
                }
            }

            // parition into groups, only get the one that contains non-basic var
            let mut groupMap = HashMap::<usize, Vec<usize>>::default();
            for i in 0..unionfind.size() {
                if hasNonBasicVar[i] {
                    let leader = unionfind.find(i);
                    groupMap.entry(leader).or_insert(vec![]).push(i);
                }
            }

            // for each group, define new chc
            for (_, group) in groupMap {
                let mut basicVars: HashSet<Slot> = HashSet::default();
                for i in &group {
                    let appId = childAppIds[*i];
                    for var in appId.slots() {
                        if !isNonBasicVar(&mergeVarTypes[&var]) {
                            basicVars.insert(var);
                        }
                    }
                }

                let mut children: Vec<_> =
                    group.clone().into_iter().map(|i| childAppIds[i]).collect();
                children.sort();
                debug!("from {:?} children after sort {:?}", rootAppId.id, children);

                let dummyEnode = CHC::New(
                    id("(pred <>)", eg),
                    id("(true)", eg),
                    children
                        .clone()
                        .into_iter()
                        .map(|a| AppliedIdOrStar::AppliedId(a.clone()))
                        .collect(),
                );
                let (dummyEnodeSh, map) = dummyEnode.weak_shape();
                let mut basicVars: Vec<_> =
                    basicVars.into_iter().map(|s| map.inverse()[s]).collect();

                debug!("dummyEnode root {:?} shape {:#?}", rootAppId.id, dummyEnode);

                basicVars.sort();

                debug!("mergeVarTypes {mergeVarTypes:?}");
                debug!("map {:?}", map);

                debug!("sorted basicVars {basicVars:?}");
                let basicVarsStr = basicVars
                    .into_iter()
                    .map(|s| generateVar(&s.to_string(), mergeVarTypes[&map[s]].clone()))
                    .collect::<Vec<_>>()
                    .join(" ");
                let syntax = format!("(pred <{basicVarsStr}>)");

                let oldLen = eg.total_number_of_nodes();
                let counter = gCounter.load(Ordering::SeqCst);

                let mut childrenStr = "".to_string();
                let mut newSubst = Subst::default();
                for i in 0..children.len() {
                    newSubst.insert(
                        format!("x{}", i),
                        children[i].clone().apply_slotmap(&map.inverse()),
                    );
                    childrenStr += &format!("?x{} ", i);
                }
                let newENodeStr = format!("(new {syntax} (true) <{childrenStr}>)");

                debug!("define_from_{}_{}", rootAppId.id, counter);
                debug!("newENodeStr {newENodeStr:?}");
                debug!("newSubst {newSubst:#?}");

                let newENodeAppId =
                    pattern_subst(eg, &Pattern::parse(&newENodeStr).unwrap(), &newSubst);

                if eg.total_number_of_nodes() == oldLen {
                    continue;
                }
                // TODO: does the use of global load & store hurt performance?

                let itf = id(
                    &format!(
                        "(interface define_from_{}_{} {syntax} 2)",
                        rootAppId.id, counter
                    ),
                    eg,
                );
                eg.union(&newENodeAppId, &itf);
                gCounter.store(counter + 1, Ordering::SeqCst);

                let composeEnode = CHC::Compose(vec![AppliedIdOrStar::AppliedId(newENodeAppId)]);
                let composeAppId = eg.add(composeEnode);
                debug!("define new {:?}", composeAppId);
            }
        }
    });

    RewriteT { searcher, applier }.into()
}

// TODO: add rule for rearrangement in compose and new children?
pub fn getAllRewrites() -> Vec<CHCRewrite> {
    vec![
        unfold(),
        newChildrenPermute(),
        composeChildrenPermute(),
        defineFromSharingBlock(),
    ]
}
