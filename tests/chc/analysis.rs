use core::error;
use std::cmp::min;

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
    // pub varTypes: BTreeMap<Slot, VarType>,
    varTypes: Vec<VarType>,
    pub functionalInfo: FunctionalInfo,
}

impl CHCData {
    pub fn varTypes(&self) -> &Vec<VarType> {
        &self.varTypes
    }

    pub fn varTypesMut(&mut self) -> &mut Vec<VarType> {
        &mut self.varTypes
    }
}

// pub fn aggregateVarType(sh: &CHC, eg: &CHCEGraph) -> BTreeMap<Slot, VarType> {
//     let sh = transformToEgraphNameSpace(sh, eg);
//     let sh = eg.find_enode(&sh);
//     let mut slots = sh.slots();
//     let appIds = sh.applied_id_occurrences();
//     let mut varTypes = BTreeMap::default();
//     for s in slots {
//         for app in &appIds {
//             for (from, to) in app.m.iter() {
//                 if to == s {
//                     let childEclassData = eg.analysis_data(app.id);
//                     if (childEclassData.varTypes.get(&from).is_none()) {
//                         app.fullDump();
//                         eg.find_applied_id(app).fullDump();
//                         println!("childEclass {:?}", eg.eclass(app.id));
//                     }
//                     let childSlotType = childEclassData.varTypes.get(&from).unwrap();
//                     varTypes
//                         .entry(s)
//                         .and_modify(|vt: &mut VarType| assert!(vt == childSlotType))
//                         .or_insert(childSlotType.clone());
//                 }
//             }
//         }
//     }

//     if appIds.iter().any(|app| app.len() != 0) {
//         if varTypes.len() == 0 {
//             for app in appIds {
//                 println!("app {:?}", app);
//                 println!("{:?}", eg.eclass(app.id));
//             }
//             panic!();
//         }
//     }

//     assert_eq!(sh.slots(), varTypes.keys().copied().collect());

//     varTypes
// }

pub fn getInterfaceVarType(sh: &CHC, eg: &CHCEGraph, slots: &Vec<Slot>) -> Vec<VarType> {
    let sh = eg.find_enode(&sh);
    let appIds = sh.applied_id_occurrences();
    let mut varTypes = BTreeMap::default();

    trace!("getInterfaceVarType {sh:?}");
    trace!("getInterfaceVarType {slots:?}");
    for app in &appIds {
        for (i, (_, to)) in app.m.iter().enumerate() {
            let childEclassData = eg.analysis_data(app.id);
            let childSlotType = childEclassData.varTypes[i];
            varTypes
                .entry(to)
                .and_modify(|vt: &mut VarType| {
                    if *vt != childSlotType {
                        error!("egraph {eg:?}");
                        error!(
                            "culprint child eclass {:?} {:?}",
                            app.id,
                            eg.eclass(app.id).unwrap()
                        );
                        error!("sh {sh:?}");

                        assert_eq!(*vt, childSlotType);
                    }
                })
                .or_insert(childSlotType.clone());
        }
    }

    slots
        .iter()
        .map(|s| varTypes.get(s).unwrap().clone())
        .collect()
}

pub fn getAllVarTypesOfENode(sh: &CHC, eg: &CHCEGraph) -> BTreeMap<Slot, VarType> {
    let appIds = sh.applied_id_occurrences();
    let mut varTypes: BTreeMap<Slot, VarType> = BTreeMap::default();
    for app in &appIds {
        for (i, (_, to)) in app.m.iter().enumerate() {
            let childEclassData = eg.analysis_data(app.id);
            let childSlotType = childEclassData.varTypes[i];

            varTypes
                .entry(to)
                .and_modify(|vt: &mut VarType| {
                    if *vt != childSlotType {
                        error!("egraph {eg:?}");
                        error!(
                            "culprint child eclass {:?} {:?}",
                            app.id,
                            eg.eclass(app.id).unwrap()
                        );
                        error!("sh {sh:?}");

                        assert_eq!(*vt, childSlotType);
                    }
                })
                .or_insert(childSlotType.clone());
        }
    }

    varTypes
}

pub fn getAllVarTypesInEClass(id: Id, eg: &CHCEGraph) -> BTreeMap<Slot, VarType> {
    let mut varTypes: BTreeMap<Slot, VarType> = BTreeMap::default();
    for (sh, _) in eg.eclass(id).unwrap().nodes.iter() {
        let appIds = sh.applied_id_occurrences();
        for app in &appIds {
            for (i, (_, to)) in app.m.iter().enumerate() {
                let childEclassData = eg.analysis_data(app.id);
                let childSlotType = childEclassData.varTypes[i];
                varTypes
                    .entry(to)
                    .and_modify(|vt: &mut VarType| assert!(*vt == childSlotType))
                    .or_insert(childSlotType.clone());
            }
        }
    }

    varTypes
}

pub fn getVarTypesAfterShrinked(
    appIdBefore: &AppliedId,
    shrinkedSlots: &SmallHashSet<Slot>,
    eg: &mut CHCEGraph,
) -> Vec<VarType> {
    trace!("updating varType of {:?}", appIdBefore.id);
    appIdBefore
        .m
        .iter()
        .enumerate()
        .filter(|(_, (_, a))| shrinkedSlots.contains(a))
        .map(|(i, _)| eg.analysis_data(appIdBefore.id).varTypes[i].clone())
        .collect::<Vec<_>>()
}

fn transformToEgraphNameSpace(sh: &CHC, eg: &CHCEGraph) -> CHC {
    if let Some(appId) = eg.lookup(sh) {
        return eg.getExactENodeInEGraph(sh);
    }

    sh.clone()
}

// fn CHCDataForPrimitiveVar(sh: &CHC, eg: &CHCEGraph, returnType: VarType) -> CHCData {
//     let sh = transformToEgraphNameSpace(sh, eg);
//     let mut hm = BTreeMap::default();
//     hm.insert(*sh.slots().iter().next().unwrap(), returnType);
//     CHCData {
//         predNames: HashSet::default(),
//         varTypes: hm,
//         functionalInfo: FunctionalInfo::default(),
//     }
// }

fn CHCDataForPrimitiveVar(sh: &CHC, eg: &CHCEGraph, returnType: VarType) -> CHCData {
    let sh = transformToEgraphNameSpace(sh, eg);
    assert!(sh.slots().len() == 1);
    CHCData {
        predNames: HashSet::default(),
        varTypes: vec![returnType],
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

    // fn merge(x: CHCData, y: CHCData, from: Id, to: Option<Id>, eg: &CHCEGraph) -> CHCData {
    //     let xClone = x.clone();
    //     let yClone = y.clone();

    //     // if to.is_some() {
    //     //     assert_eq!(from, to.unwrap());
    //     // }

    //     let newPredNames = mergePredNames(&x.predNames, &y.predNames);

    //     let mut newVarTypes = x.varTypes.clone();
    //     for (var, yVarType) in y.varTypes.iter() {
    //         if let Some(thisType) = newVarTypes.get(&var) {
    //             assert!(yVarType == thisType);
    //         } else {
    //             newVarTypes.insert(var.clone(), yVarType.clone());
    //         }
    //     }

    //     // let mut newVarTypes: BTreeMap<Slot, VarType> = BTreeMap::default();
    //     // let useEclass = if to.is_some() { to.unwrap() } else { from };
    //     // for enode in eg.enodes(useEclass) {
    //     //     match enode {
    //     //         CHC::Int(_) => {
    //     //             newVarTypes.extend(CHCDataForPrimitiveVar(&enode, eg, VarType::Int).varTypes)
    //     //         }
    //     //         CHC::Node(_) => {
    //     //             newVarTypes.extend(CHCDataForPrimitiveVar(&enode, eg, VarType::Node).varTypes)
    //     //         }
    //     //         CHC::Var(_) => newVarTypes
    //     //             .extend(CHCDataForPrimitiveVar(&enode, eg, VarType::Unknown).varTypes),
    //     //         _ => newVarTypes.extend(aggregateVarType(&enode, eg)),
    //     //     };
    //     // }

    //     let mut eclassSlots = eg.allSlots(from);
    //     if to.is_some() {
    //         eclassSlots.extend(eg.allSlots(to.unwrap()));
    //     }

    //     trace!("newVarTypes before filter {newVarTypes:?}");
    //     let newVarTypes: BTreeMap<Slot, VarType> = newVarTypes
    //         .into_iter()
    //         .filter(|(s, vt)| eclassSlots.contains(&s))
    //         .collect();

    //     if (x.varTypes.len() != 0 || y.varTypes.len() != 0) {
    //         if newVarTypes.len() == 0 && eclassSlots.len() != 0 {
    //             error!("x {xClone:#?}");
    //             error!("y {yClone:#?}");
    //             error!("from {:?}", eg.eclass(from));
    //             if to.is_some() {
    //                 error!("to {:?}", eg.eclass(to.unwrap()));
    //             }
    //             error!("eclassSlots {eclassSlots:#?}");
    //             // println!("eclassSlots {eclassSlots:#?}");

    //             assert!(newVarTypes.len() != 0);
    //         }
    //     }

    //     // println!("merging {} {:?} result {:#?}", from, to, newVarTypes);
    //     // println!("from {:?}", eg.eclass(from));
    //     // if to.is_some() {
    //     //     println!("to {:?}", eg.eclass(to.unwrap()));
    //     // }

    //     CHCData {
    //         predNames: newPredNames,
    //         varTypes: newVarTypes,
    //         functionalInfo: mergeFunctionalInfo(x.functionalInfo, y.functionalInfo),
    //     }
    // }

    // TODO: we cannot assume that the interface slots of eclass are always ordered the same after merging
    // Hence, ordering of varTypes in a vector might not work
    fn merge(x: CHCData, y: CHCData, from: Id, to: Option<Id>, eg: &CHCEGraph) -> CHCData {
        let mut varTypes = if to.is_some() {
            let ret = eg
                .eclass(to.unwrap())
                .unwrap()
                .analysis_data
                .varTypes
                .clone();

            ret
        } else {
            eg.eclass(from).unwrap().analysis_data.varTypes.clone()
        };

        if x.varTypes.len() < varTypes.len() {
            varTypes = x.varTypes.clone();
        }

        if y.varTypes.len() < varTypes.len() {
            varTypes = y.varTypes.clone();
        }

        CHCData {
            predNames: mergePredNames(&x.predNames, &y.predNames),
            varTypes: varTypes,
            functionalInfo: mergeFunctionalInfo(x.functionalInfo, y.functionalInfo),
        }
    }

    fn make(eg: &CHCEGraph, sh: &CHC, slots: &Vec<Slot>) -> CHCData {
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
                    varTypes: getInterfaceVarType(sh, eg, &(slots.clone().into())),
                    functionalInfo: FunctionalInfo::default(),
                }
            }
            CHC::IntType(_) => CHCDataForPrimitiveVar(sh, eg, VarType::Int),
            CHC::NodeType(_) => CHCDataForPrimitiveVar(sh, eg, VarType::Node),
            CHC::ListType(_) => CHCDataForPrimitiveVar(sh, eg, VarType::List),
            _ => CHCData {
                predNames: HashSet::default(),
                varTypes: getInterfaceVarType(sh, eg, &(slots.clone().into())),
                functionalInfo: FunctionalInfo::default(),
            },
        };
        trace!("calling make on {:?}", sh);
        trace!("get data {chcData:?}");

        if slots.len() != 0 && chcData.varTypes.len() == 0 {
            error!("varTypes len 0");
            error!("chcData {chcData:?}");
            error!("enode {:?}", sh);
            error!("enode children:");
            for child in sh.applied_id_occurrences() {
                error!("child eclass {:?}", eg.eclass(child.id));
            }
            panic!("slots is not empty, but varTypes is empty");
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
