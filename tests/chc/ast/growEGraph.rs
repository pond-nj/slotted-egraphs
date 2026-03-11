use log::{info, trace};
use rustsat::{
    instances::{BasicVarManager, Cnf, SatInstance},
    solvers::{Solve, SolverResult},
    types::{Clause, Lit, TernaryVal},
};
use rustsat_minisat::core::Minisat;

use super::*;

// fn createDummy(predName: &str, args: &Vec<String>, props: &BTreeMap<String, PredProp>) -> String {
//     let syntax = format!("(pred <{}>)", args.join(" "));
//     format!(
//         "(composeInit {predName} {syntax} ({}) <{}>)",
//         props.get(predName).unwrap().functional,
//         props
//             .get(predName)
//             .unwrap()
//             .outputIdx
//             .iter()
//             .map(|i| format!("{}", i))
//             .collect::<Vec<_>>()
//             .join(" ")
//     )
// }

fn checkComposeMerge(eg: &CHCEGraph) {
    for id in eg.ids() {
        let enodes = eg.enodes(id);
        if enodes.iter().any(|e| matches!(e, CHC::ComposeInit(..))) {
            assert!(enodes.iter().any(|e| matches!(e, CHC::Compose(..))));
        }
    }

    trace!("checkComposeMerge done");
}

pub fn prepareRules(fname: &str) -> (CHCAst, BTreeMap<String, Vec<CHCRule>>) {
    let mut chcs = parse(fname);

    for rule in chcs.rules.iter_mut() {
        debug!("rule before {rule:?}");
        let mut count = 0;
        let (newConstr1, subst) = rule.head.renameHead(&mut count);
        debug!("subst {subst:?}");
        rule.substitute(&subst, true);

        let newConstr2: Vec<Constr> = rule
            .pred_apps
            .iter_mut()
            .flat_map(|p| p.renameTerm(&mut count))
            .collect();

        rule.constr.extend(newConstr1);
        rule.constr.extend(newConstr2);
        debug!("rule after {rule:?}");
    }

    let mut predNames: BTreeSet<String> = chcs
        .rules
        .iter()
        .map(|r| r.head.pred_name.clone())
        .collect();
    assert_eq!(predNames.len(), chcs.preds.len());

    let mut rulesByPred: BTreeMap<String, Vec<CHCRule>> = BTreeMap::new();
    for rule in chcs.rules.iter() {
        rulesByPred
            .entry(rule.head.pred_name.clone())
            .or_insert(vec![])
            .push(rule.clone());
    }

    (chcs, rulesByPred)
}

pub fn getConstrTypes(
    rule: &CHCRule,
    props: &PredProp,
    chcs: &CHCAst,
) -> BTreeMap<CHCVar, ArgType> {
    let CHCRule {
        head,
        constr,
        pred_apps,
        original,
    } = rule;

    let mut typeMap = BTreeMap::new();
    head.retrieveTypes(&mut typeMap, &props);
    for b in pred_apps.iter() {
        b.retrieveTypes(&mut typeMap, &chcs.preds.get(&b.pred_name).unwrap());
    }
    for c in constr.iter() {
        c.propagateTypeUp(&mut typeMap);
    }

    typeMap
}

pub fn growEGraph(fname: &str, eg: &mut CHCEGraph) {
    info!("growing EGraph from {}", fname);
    let (chcs, rulesByPred) = prepareRules(fname);
    let none = ();
    for (predName, rules) in rulesByPred {
        let props: &PredProp = chcs.preds.get(&predName).unwrap();
        let mut composeChildren = Vec::new();
        let mut dummyCompose = None;
        let mut headSlots: Option<Vec<_>> = None;
        for rule in rules {
            let CHCRule {
                head,
                constr,
                pred_apps,
                original,
            } = &rule;

            info!("input line {}", original);
            let typeMap = getConstrTypes(&rule, props, &chcs);
            debug!("typeMap {:?}", typeMap);

            let expr = rule.toSExpr(&chcs.preds, &typeMap);
            info!("rule {}\n", expr);
            composeChildren.push(expr.clone());
            let newENodeId = eg.addExpr(&expr);

            let thisHeadSlots = head
                .args
                .iter()
                .map(|a| a.getVarFormOnly().unwrap().toSlot())
                .collect();

            if let Some(headSlots) = &headSlots {
                if CHECKS {
                    assert_eq!(headSlots, &thisHeadSlots);
                }
            } else {
                headSlots = Some(thisHeadSlots);
            };
            let appId = &eg.find_applied_id(&newENodeId);
            let shrinkSlots = headSlots.clone().unwrap().into_iter().collect();
            eg.shrink_slots(appId, &shrinkSlots, none);
            *eg.analysis_data_mut(appId.id).varTypesMut() =
                getVarTypesAfterShrinked(&appId, &shrinkSlots, eg);

            eg.analysis_data_mut(eg.find_applied_id(&newENodeId).id)
                .predNames
                .insert(predName.clone());

            dummyCompose = Some(head.toTailSExpr(props, &typeMap));
        }
        let composeExpr = format!("(compose <{}>)", composeChildren.join(" "));

        let dummyAppId = eg.addExpr(&dummyCompose.unwrap());
        let composeAppId = eg.addExpr(&composeExpr);
        eg.union(&composeAppId, &dummyAppId);
        info!(
            "{predName} has compose Id {:?}",
            eg.find_applied_id(&composeAppId).id
        );
        eg.shrink_slots(
            &eg.find_applied_id(&composeAppId),
            &headSlots.unwrap().into_iter().collect(),
            none,
        );

        eg.analysis_data_mut(eg.find_applied_id(&composeAppId).id)
            .predNames
            .insert(predName.clone());
    }

    info!("Egraph after growEGraph");
    // eg.printUnionFind();
    dumpCHCEGraph(eg);

    if CHECKS {
        checkComposeMerge(eg);
    }
    // ()
}

// If not called on this predName before, return an expression that shows how the chc definition of this predName is defined.
// Otherwise, just return a variable.
pub fn getExprRecur(
    predName: &String,
    chcs: &CHCAst,
    rulesByPred: &BTreeMap<String, Vec<CHCRule>>,
    mapping: &mut BTreeMap<String, String>,
) -> String {
    if mapping.contains_key(predName) {
        return format!("?{}", predName);
    }

    mapping.insert(predName.clone(), "".to_owned());
    let rules = rulesByPred.get(predName).unwrap();
    let props: &PredProp = chcs.preds.get(predName).unwrap();
    let mut composeChildren = Vec::new();
    for rule in rules {
        let CHCRule {
            head,
            constr,
            pred_apps,
            original,
        } = rule;

        let mut typeMap = getConstrTypes(rule, props, chcs);
        let expr = format!(
            "(new {} {} {})",
            rule.head.toHeadSExpr(&typeMap),
            format!(
                "(and <{}>)",
                rule.constr
                    .iter()
                    .map(|c| c.toSExpr(&typeMap))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            format!(
                "<{}>",
                rule.pred_apps
                    .iter()
                    .map(|p| getExprRecur(&p.pred_name, chcs, rulesByPred, mapping))
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        );
        composeChildren.push(expr);
    }

    let composeExpr = format!("(compose <{}>)", composeChildren.join(" "));
    mapping.insert(predName.clone(), composeExpr.clone());
    composeExpr
}

pub fn getPredExpr(
    predName: &String,
    rules: &Vec<CHCRule>,
    chcs: &CHCAst,
) -> (String, BTreeMap<String, Vec<String>>) {
    let props: &PredProp = chcs.preds.get(predName).unwrap();
    let mut composeChildren = Vec::new();
    let mut patternVars = BTreeMap::new();

    for (i, rule) in rules.iter().enumerate() {
        let mut rule = rule.clone();
        let mut internalVars = BTreeSet::new();
        rule.getInternalVars(&mut internalVars);

        let mut renameMap = BTreeMap::new();
        for v in internalVars.iter() {
            let newVar = CHCVar::Str(format!("{}_{i}", v));
            renameMap.insert(v.clone(), newVar);
        }
        rule.substitute(&renameMap, false);

        let CHCRule {
            head,
            constr,
            pred_apps,
            original,
        } = &rule;

        let mut typeMap = getConstrTypes(&rule, props, chcs);
        let expr = format!(
            "(new {} {} {})",
            rule.head.toHeadSExpr(&typeMap),
            format!(
                "(and <{}>)",
                rule.constr
                    .iter()
                    .map(|c| c.toSExpr(&typeMap))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            format!(
                "<{}>",
                rule.pred_apps
                    .iter()
                    .map(|p| {
                        let newVar = format!("{}_{i}", p.pred_name);
                        patternVars
                            .entry(p.pred_name.clone())
                            .or_insert(vec![])
                            .push(newVar.clone());
                        format!("?{}", newVar)
                    })
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        );
        composeChildren.push(expr);
    }

    let composeExpr = format!("(compose <{}>)", composeChildren.join(" "));
    (composeExpr, patternVars)
}

// TODO: this function is buggy, because when creating child expr, we have to rename the child vars also
// but the renaming logic is not implemented yet?
pub fn checkCHCExistsByExpr(fname: &str, eg: &CHCEGraph) {
    let (chcs, rulesByPred): (CHCAst, BTreeMap<String, Vec<CHCRule>>) = prepareRules(fname);

    let mut exprMapping = BTreeMap::new();
    let expectedExpr = getExprRecur(
        &"incorrect".to_owned(),
        &chcs,
        &rulesByPred,
        &mut exprMapping,
    );
    info!("getExpr {expectedExpr}");

    let res: Vec<(Subst, Id)> = ematchQueryall(&eg, &Pattern::parse(&expectedExpr).unwrap());
    assert!(res.len() > 0);

    let mut found = false;
    'record: for (subst, eclassId) in res {
        for (predName, expr) in exprMapping.iter() {
            let pattern: Pattern<CHC> = Pattern::parse(&expr).unwrap();
            let result = eg.lookupPatternWithSubst(&pattern, &subst);
            let appId = result.unwrap();
            if appId.id != subst.get(&format!("?{}", predName)).unwrap().id {
                continue 'record;
            }
        }

        found = true;
    }

    assert!(found);
}

pub fn checkCHCExists(fname: &str, eg: &CHCEGraph) {
    let (chcs, rulesByPred): (CHCAst, BTreeMap<String, Vec<CHCRule>>) = prepareRules(fname);

    let mut predToEclassId = BTreeMap::new();

    let mut updatePredToEclassId = |predName: &String, possibilities: &BTreeSet<Id>| {
        let oldEntry = predToEclassId
            .entry(predName.clone())
            .or_insert(possibilities.clone());

        *oldEntry = oldEntry.intersection(&possibilities).cloned().collect();
    };

    let mut predNamesToIdx = BTreeMap::new();
    for (i, predName) in chcs.preds.keys().enumerate() {
        predNamesToIdx.insert(predName.clone(), i);
    }

    let mut eclassIdToIdx = BTreeMap::new();
    let mut andAnswers = vec![];
    for (predName, rules) in rulesByPred {
        let (expr, patternVars) = getPredExpr(&predName, &rules, &chcs);

        info!("expr {expr}\n");

        let res: Vec<(Subst, Id)> = ematchQueryall(&eg, &Pattern::parse(&expr).unwrap());
        assert!(
            res.len() > 0,
            "predname {predName}, expr {expr} has no result"
        );

        let mut orAnswers = BTreeSet::new();
        for (subst, rootEclassId) in res {
            let eclassIdToIdxLen = eclassIdToIdx.len();
            eclassIdToIdx
                .entry(rootEclassId)
                .or_insert(eclassIdToIdxLen);

            let mut predNameToEclassId = BTreeMap::new();
            for (bodyPredName, vars) in patternVars.iter() {
                let mut eclassId = None;

                for var in vars.iter() {
                    if eclassId.is_none() {
                        eclassId = Some(subst.get(var).unwrap().id);
                    }

                    assert_eq!(eclassId.unwrap(), subst.get(var).unwrap().id);
                }

                let eclassId = eclassId.unwrap();

                let eclassIdToIdxLen = eclassIdToIdx.len();
                eclassIdToIdx.entry(eclassId).or_insert(eclassIdToIdxLen);
                predNameToEclassId.insert(bodyPredName.clone(), eclassId);
            }

            predNameToEclassId
                .entry(predName.clone())
                .or_insert(rootEclassId);

            assert_eq!(predNameToEclassId[&predName], rootEclassId);

            orAnswers.insert(predNameToEclassId);
        }
        andAnswers.push(orAnswers);
    }

    let varIdx = |predName: &String, eclassId: &Id| {
        let predNameIdx = predNamesToIdx.get(predName).unwrap();
        let eclassIdIdx = eclassIdToIdx.get(eclassId).unwrap();
        predNameIdx * eclassIdToIdx.len() + eclassIdIdx
    };

    // row is predName
    // col is eclassId
    let mut allCnfs: Cnf = Cnf::new();
    let mut solver = Minisat::default();
    let mut count = predNamesToIdx.len() * eclassIdToIdx.len();
    for orAnswers in andAnswers {
        let mut dnf: Vec<Vec<usize>> = Vec::new();
        for assignment in orAnswers.iter() {
            let mut dnfClause: Vec<usize> = Vec::new();
            for (predName, eclassId) in assignment.iter() {
                dnfClause.push(varIdx(predName, eclassId));
            }
            dnf.push(dnfClause);
        }
        for cnf in dnfToCnfByTseitin(&dnf, &mut count) {
            allCnfs.add_clause(cnf);
        }
    }

    for (predName, predNameIdx) in predNamesToIdx.iter() {
        for (eclassId1, eclassIdIdx1) in eclassIdToIdx.iter() {
            for (eclassId2, eclassIdIdx2) in eclassIdToIdx.iter() {
                if eclassIdIdx1 == eclassIdIdx2 {
                    continue;
                }
                let mut clause = Clause::new();
                clause.add(Lit::negative(varIdx(&predName, &eclassId1) as u32));
                clause.add(Lit::negative(varIdx(&predName, &eclassId2) as u32));
                allCnfs.add_clause(clause);
            }
        }
    }

    for (eclassId, eclassIdIdx) in eclassIdToIdx.iter() {
        for (predName1, predNameIdx1) in predNamesToIdx.iter() {
            for (predName2, predNameIdx2) in predNamesToIdx.iter() {
                if predNameIdx1 == predNameIdx2 {
                    continue;
                }
                let mut clause = Clause::new();
                clause.add(Lit::negative(varIdx(&predName1, &eclassId) as u32));
                clause.add(Lit::negative(varIdx(&predName2, &eclassId) as u32));
                allCnfs.add_clause(clause);
            }
        }
    }

    solver.add_cnf(allCnfs).unwrap();
    let mut sols = vec![];
    while solver.solve().unwrap() == SolverResult::Sat {
        let sol = solver.full_solution().unwrap();
        let mut assignments = BTreeMap::new();
        let mut blockingClause = Clause::new();
        for (predName, predNameIdx) in predNamesToIdx.iter() {
            for (eclassId, eclassIdIdx) in eclassIdToIdx.iter() {
                let lit = Lit::positive(varIdx(&predName, &eclassId) as u32);
                match sol[lit.var()] {
                    TernaryVal::True => {
                        assignments.entry(predName).or_insert(eclassId);
                        blockingClause.add(Lit::negative(lit.vidx32()));
                    }
                    TernaryVal::False => {
                        blockingClause.add(Lit::positive(lit.vidx32()));
                    }
                    TernaryVal::DontCare => {
                        panic!();
                    }
                }
            }
        }
        solver.add_clause(blockingClause);
        sols.push(assignments);
    }
    info!("sols {sols:?}");
    assert!(sols.len() > 0);
}
