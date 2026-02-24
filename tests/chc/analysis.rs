use log::{error, trace};

use super::*;

#[derive(Default)]
pub struct CHCAnalysis;

// The implementation in "functionalTransformation" assumes that all the indices between 0 and max(outputIdx)
// if it's not the output, then it will be the input
#[derive(Default, Eq, PartialEq, Clone, Debug)]
pub struct FunctionalInfo {
    pub functional: bool,
    pub outputIdx: Vec<usize>,
}

// TODO: implement Debug to CHC clause using syn_enode
#[derive(Eq, PartialEq, Clone, Debug, Default)]
pub struct CHCData {
    pub predNames: HashSet<String>,
    pub varTypes: BTreeMap<Slot, VarType>,
    pub functionalInfo: FunctionalInfo,
}

pub fn aggregateVarType(sh: &CHC, eg: &CHCEGraph) -> BTreeMap<Slot, VarType> {
    let sh = transformToEgraphNameSpace(sh, eg);
    let sh = eg.find_enode(&sh);
    let mut slots = sh.slots();
    let appIds = sh.applied_id_occurrences();
    let mut varTypes = BTreeMap::default();
    for s in slots {
        for app in &appIds {
            for (from, to) in app.m.iter() {
                if to == s {
                    let childEclassData = eg.analysis_data(app.id);
                    if (childEclassData.varTypes.get(&from).is_none()) {
                        app.fullDump();
                        eg.find_applied_id(app).fullDump();
                        println!("childEclass {:?}", eg.eclass(app.id));
                    }
                    let childSlotType = childEclassData.varTypes.get(&from).unwrap();
                    varTypes
                        .entry(s)
                        .and_modify(|vt: &mut VarType| assert!(vt == childSlotType))
                        .or_insert(childSlotType.clone());
                }
            }
        }
    }

    if appIds.iter().any(|app| app.len() != 0) {
        if varTypes.len() == 0 {
            for app in appIds {
                println!("app {:?}", app);
                println!("{:?}", eg.eclass(app.id));
            }
            panic!();
        }
    }

    assert_eq!(sh.slots(), varTypes.keys().copied().collect());

    varTypes
}

fn transformToEgraphNameSpace(sh: &CHC, eg: &CHCEGraph) -> CHC {
    if let Some(appId) = eg.lookup(sh) {
        return eg.getExactENodeInEGraph(sh);
    }

    sh.clone()
}

fn CHCDataForPrimitiveVar(sh: &CHC, eg: &CHCEGraph, returnType: VarType) -> CHCData {
    let sh = transformToEgraphNameSpace(sh, eg);
    let mut hm = BTreeMap::default();
    hm.insert(*sh.slots().iter().next().unwrap(), returnType);
    CHCData {
        predNames: HashSet::default(),
        varTypes: hm,
        functionalInfo: FunctionalInfo::default(),
    }
}

pub fn getBoolVal(eclassId: &Id, eg: &CHCEGraph) -> bool {
    let enodes = eg.enodes(*eclassId);
    let firstENode = enodes.iter().next().unwrap();
    match firstENode {
        CHC::True() => true,
        CHC::And(v) => {
            assert!(v.len() == 0);
            true
        }
        CHC::False() => false,
        _ => {
            println!("{:#?}", enodes);
            panic!()
        }
    }
}

fn mergeFunctionalInfo(x: FunctionalInfo, y: FunctionalInfo) -> FunctionalInfo {
    let mut functionalInfo = None;
    if x.functional && y.functional {
        assert!(x == y);
        functionalInfo = Some(x);
    } else if !x.functional {
        assert!(x.outputIdx.len() == 0);
        functionalInfo = Some(y);
    } else {
        assert!(y.outputIdx.len() == 0);
        functionalInfo = Some(x);
    }

    functionalInfo.unwrap()
}

fn mergePredNames(xPredNames: &HashSet<String>, yPredNames: &HashSet<String>) -> HashSet<String> {
    let mut newPredNames = HashSet::<String>::default();
    let xLen = xPredNames.len();
    let yLen = yPredNames.len();
    newPredNames.extend(yPredNames.clone());
    newPredNames.extend(xPredNames.clone());
    newPredNames
}

// TODO2: varType not propagate up
// TODO: internal var for each eclass
impl Analysis<CHC> for CHCAnalysis {
    type Data = CHCData;

    fn merge(x: CHCData, y: CHCData, from: Id, to: Option<Id>, eg: &CHCEGraph) -> CHCData {
        let xClone = x.clone();
        let yClone = y.clone();

        // if to.is_some() {
        //     assert_eq!(from, to.unwrap());
        // }

        let newPredNames = mergePredNames(&x.predNames, &y.predNames);

        let mut newVarTypes = x.varTypes.clone();
        for (var, yVarType) in y.varTypes.iter() {
            if let Some(thisType) = newVarTypes.get(&var) {
                assert!(yVarType == thisType);
            } else {
                newVarTypes.insert(var.clone(), yVarType.clone());
            }
        }

        // let mut newVarTypes: BTreeMap<Slot, VarType> = BTreeMap::default();
        // let useEclass = if to.is_some() { to.unwrap() } else { from };
        // for enode in eg.enodes(useEclass) {
        //     match enode {
        //         CHC::Int(_) => {
        //             newVarTypes.extend(CHCDataForPrimitiveVar(&enode, eg, VarType::Int).varTypes)
        //         }
        //         CHC::Node(_) => {
        //             newVarTypes.extend(CHCDataForPrimitiveVar(&enode, eg, VarType::Node).varTypes)
        //         }
        //         CHC::Var(_) => newVarTypes
        //             .extend(CHCDataForPrimitiveVar(&enode, eg, VarType::Unknown).varTypes),
        //         _ => newVarTypes.extend(aggregateVarType(&enode, eg)),
        //     };
        // }

        let mut eclassSlots = eg.allSlots(from);
        if to.is_some() {
            eclassSlots.extend(eg.allSlots(to.unwrap()));
        }
        let newVarTypes: BTreeMap<Slot, VarType> = newVarTypes
            .into_iter()
            .filter(|(s, vt)| eclassSlots.contains(&s))
            .collect();

        if (x.varTypes.len() != 0 || y.varTypes.len() != 0) {
            if newVarTypes.len() == 0 {
                error!("x {xClone:#?}");
                error!("y {yClone:#?}");
                error!("from {:?}", eg.eclass(from));
                if to.is_some() {
                    error!("to {:?}", eg.eclass(to.unwrap()));
                }
                // println!("eclassSlots {eclassSlots:#?}");

                assert!(newVarTypes.len() != 0);
            }
        }

        // println!("merging {} {:?} result {:#?}", from, to, newVarTypes);
        // println!("from {:?}", eg.eclass(from));
        // if to.is_some() {
        //     println!("to {:?}", eg.eclass(to.unwrap()));
        // }

        CHCData {
            predNames: newPredNames,
            varTypes: newVarTypes,
            functionalInfo: mergeFunctionalInfo(x.functionalInfo, y.functionalInfo),
        }
    }

    fn make(eg: &CHCEGraph, sh: &CHC) -> CHCData {
        trace!("calling make on {:?}", sh);
        let mut chcData = match sh {
            CHC::ComposeInit(predNameId, predSyntaxId, _, _) => {
                let stringEnodes = eg.enodes(predNameId.id);
                assert!(stringEnodes.len() == 1);
                let stringEnode = stringEnodes.iter().next().unwrap();
                let CHC::PredName(predName) = stringEnode else {
                    panic!();
                };
                let mut predNames = HashSet::default();
                predNames.insert(predName.to_owned());

                CHCData {
                    predNames,
                    varTypes: aggregateVarType(sh, eg),
                    functionalInfo: FunctionalInfo::default(),
                }
            }
            CHC::IntType(_) => CHCDataForPrimitiveVar(sh, eg, VarType::Int),
            CHC::NodeType(_) => CHCDataForPrimitiveVar(sh, eg, VarType::Node),
            CHC::ListType(_) => CHCDataForPrimitiveVar(sh, eg, VarType::List),
            _ => CHCData {
                predNames: HashSet::default(),
                varTypes: aggregateVarType(sh, eg),
                functionalInfo: FunctionalInfo::default(),
            },
        };

        if sh.slots().len() != 0 && chcData.varTypes.len() == 0 {
            error!("varTypes len 0");
            error!("enode {:?}", sh);
            error!("enode children:");
            for child in sh.applied_id_occurrences() {
                error!("child eclass {:?}", eg.eclass(child.id));
            }
        }

        let functionalInfo = match sh {
            CHC::ComposeInit(_, _, functional, outputIdxAppIds) => {
                let functional = getBoolVal(&functional.id, eg);

                let mut outputIdx: Vec<usize> = vec![];
                for appId in outputIdxAppIds.iter() {
                    let enode = getSingleENode(&appId.id, eg);
                    match enode {
                        CHC::Number(idx) => {
                            outputIdx.push(idx as usize);
                        }
                        _ => panic!(),
                    }
                }

                FunctionalInfo {
                    functional,
                    outputIdx,
                }
            }
            _ => FunctionalInfo::default(),
        };

        chcData.functionalInfo = functionalInfo;
        trace!("done calling make");
        chcData
    }

    fn modify(eg: &mut EGraph<CHC, Self>, i: Id) {}
}
