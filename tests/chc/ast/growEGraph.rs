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

pub fn growEGraph(fname: &str, eg: &mut CHCEGraph) {
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

    let dummyEClass = ();
    for (predName, rules) in rulesByPred {
        let props = chcs.preds.get(&predName).unwrap();
        for rule in rules {
            let CHCRule {
                head,
                constr,
                pred_apps,
                original,
            } = &rule;

            println!("original {}", original);
            println!("rule {}", rule.toSExpr(&chcs.preds));
            let mut typeMap = BTreeMap::new();
            head.retrieveTypes(&mut typeMap, &props);
            for b in pred_apps.iter() {
                b.retrieveTypes(&mut typeMap, &chcs.preds.get(&b.pred_name).unwrap());
            }
            for c in constr.iter() {
                c.propagateTypeUp(&mut typeMap);
            }
            println!("typeMap {:?}", typeMap);
        }
    }
    // ()
}
