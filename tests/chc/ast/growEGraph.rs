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
        let mut count = 0;
        let newConstr1 = rule.head.renameAll(&mut count);
        let newConstr2: Vec<Constr> = rule
            .pred_apps
            .iter_mut()
            .flat_map(|p| p.renameTerm(&mut count))
            .collect();

        rule.constr.extend(newConstr1);
        rule.constr.extend(newConstr2);
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
            debug!("typeMap {:?}", typeMap);

            let expr = rule.toSExpr(&chcs.preds, &typeMap);
            info!("rule {}\n", expr);
            composeChildren.push(expr.clone());
            let newENodeId = eg.addExpr(&expr);

            let thisHeadSlots = head
                .args
                .iter()
                .map(|a| a.getVar().unwrap().toSlot())
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

pub fn getExpr(
    predName: &String,
    chcs: &CHCAst,
    rulesByPred: &BTreeMap<String, Vec<CHCRule>>,
    written: &mut BTreeSet<String>,
) -> String {
    if written.contains(predName) {
        return format!("${}", predName);
    }

    written.insert(predName.clone());
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
                    .map(|p| getExpr(&p.pred_name, chcs, rulesByPred, written))
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        );
        composeChildren.push(expr);
    }

    let composeExpr = format!("(compose <{}>)", composeChildren.join(" "));

    composeExpr
}

pub fn checkGraphExists(fname: &str, eg: &CHCEGraph) {
    let (chcs, rulesByPred): (CHCAst, BTreeMap<String, Vec<CHCRule>>) = prepareRules(fname);

    let expectedExpr = getExpr(
        &"incorrect".to_owned(),
        &chcs,
        &rulesByPred,
        &mut BTreeSet::new(),
    );
    info!("getExpr {expectedExpr}");

    let res = ematchQueryall(&eg, &Pattern::parse(&expectedExpr).unwrap());
    assert!(res.len() > 0);

    // TODO: check that the var in this expression points to the defined eclass
}
