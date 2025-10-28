use super::*;
use crate::*;
use log::debug;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;
use union_find::{QuickUnionUf, UnionBySize, UnionFind};

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
            debug!("root eclass {:?}", eg.eclass(rootAppId.id).unwrap());
            // TODO: can we not do cloning here?
            let mut rootData = eg.analysis_data(rootAppId.id).clone();
            let star1Max = getMaxStarCount(1, &subst);
            let mut varToStarIndex: HashMap<Slot, Vec<usize>> = HashMap::default();

            debug!("subst = {subst:#?}");
            debug!("rootData = {rootData:?}");

            let mut mergeVarTypes: HashMap<Slot, VarType> = HashMap::default();
            for star1Count in 0..star1Max {
                let appId = subst.get(&starPVar(1, star1Count)).unwrap();
                debug!("appId.slots {:?}", appId.slots());
                for s in appId.slots() {
                    varToStarIndex
                        .entry(s)
                        .or_insert(vec![])
                        .push(star1Count.try_into().unwrap());
                }

                let varTypes = &eg.analysis_data(appId.id).varTypes;
                mergeVarTypes.extend(varTypes.clone().into_iter().map(|(s, vt)| (appId.m[s], vt)));
            }

            debug!("mergeVarTypes = {mergeVarTypes:#?}");
            debug!("varToStarIndex = {varToStarIndex:#?}");

            let mut unionfind: QuickUnionUf<UnionBySize> =
                QuickUnionUf::<UnionBySize>::new(star1Max as usize);
            let mut hasNonBasicVar = vec![false; star1Max as usize];

            // TODO: why rootData does not contain some var?

            for (var, star1Counts) in &varToStarIndex {
                debug!("var = {var:?}");
                let appId = subst
                    .get(&starPVar(1, *star1Counts.first().unwrap() as u32))
                    .unwrap();
                debug!("children eclass {:?} {:?}", appId.id, eg.eclass(appId.id));
                if isNonBasicVar(&mergeVarTypes[var]) {
                    let leader = varToStarIndex.get(&var).unwrap().first().unwrap();
                    for next in varToStarIndex.get(&var).unwrap() {
                        unionfind.union(*leader, *next);
                        hasNonBasicVar[*next] = true;
                    }
                }
            }

            let mut groupMap = HashMap::<usize, Vec<usize>>::default();
            for star1Count in 0..star1Max {
                if hasNonBasicVar[star1Count as usize] {
                    let groupId = unionfind.find(star1Count.try_into().unwrap());
                    groupMap
                        .entry(groupId)
                        .or_insert(vec![])
                        .push(star1Count as usize);
                }
            }

            for (_, group) in groupMap {
                let mut newSubst = Subst::default();
                let mut count = 0;
                for star1Count in &group {
                    newSubst.insert(
                        starPVar(2, count),
                        subst.get(&starPVar(1, *star1Count as u32)).unwrap().clone(),
                    );
                    count += 1;
                }

                let mut nonBasicVars: HashSet<Slot> = HashSet::default();
                for star1Count in group {
                    let appId = subst.get(&starPVar(1, star1Count as u32)).unwrap();
                    for var in appId.slots() {
                        if isNonBasicVar(&mergeVarTypes[&var]) {
                            nonBasicVars.insert(var);
                        }
                    }
                }

                let nonBasicVarStr = nonBasicVars
                    .into_iter()
                    .map(|s| generateVar(&s.to_string(), mergeVarTypes[&s].clone()))
                    .collect::<Vec<_>>()
                    .join(" ");

                debug!("nonBasicVarStr {nonBasicVarStr:?}");

                let newAppId = pattern_subst(
                    eg,
                    &Pattern::parse(&format!("(new (pred <{}>) (true) <*2>)", nonBasicVarStr))
                        .unwrap(),
                    &newSubst,
                );

                let composeEnode = CHC::Compose(vec![AppliedIdOrStar::AppliedId(newAppId)]);
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
