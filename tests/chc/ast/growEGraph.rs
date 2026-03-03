use log::{info, trace};

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

            info!("original {}", original);
            let typeMap = getConstrTypes(&rule, props, &chcs);
            debug!("rule {rule:?}");
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
        eg.shrink_slots(
            &eg.find_applied_id(&composeAppId),
            &headSlots.unwrap().into_iter().collect(),
            none,
        );

        eg.analysis_data_mut(eg.find_applied_id(&composeAppId).id)
            .predNames
            .insert(predName.clone());
    }

    debug!("end of growEGraph");
    eg.printUnionFind();
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

    for (predName, rules) in rulesByPred {
        let (expr, patternVars) = getPredExpr(&predName, &rules, &chcs);

        let res: Vec<(Subst, Id)> = ematchQueryall(&eg, &Pattern::parse(&expr).unwrap());
        assert!(
            res.len() > 0,
            "predname {predName}, expr {expr} has no result"
        );

        for (bodyPredName, vars) in patternVars {
            let mut possibilities = BTreeSet::new();
            for (subst, _) in res.iter() {
                for var in vars.iter() {
                    possibilities.insert(subst.get(var).unwrap().id);
                }
            }
            updatePredToEclassId(&predName, &possibilities);
        }
    }

    info!("possible eclass {:?}", predToEclassId);

    for (predName, possibilities) in predToEclassId {
        assert!(
            possibilities.len() > 0,
            "predName {} has no possible eclass",
            predName
        );
    }
    info!("chc {} exists", fname);
}
