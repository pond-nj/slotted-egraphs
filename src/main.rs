use slotted_egraphs::*;

use log::debug;

define_language! {
    // TODO(Pond): now children can only have max one vector
    // TODO: add dont care var?
    pub enum CHC {
        Var(Slot) = "var",
        // to specify types
        Int(Slot) = "int",
        Node(Slot) = "node",

        PredSyntax(Vec<AppliedId>) = "pred",
        New(AppliedId, AppliedId, Vec<AppliedIdOrStar>) = "new",
        Compose(Vec<AppliedIdOrStar>) = "compose",
        True() = "true",

        // node(x, l, r) has subtree l and r and element x at this node
        BiNode(AppliedId, AppliedId, AppliedId) = "binode",
        Leaf() = "leaf",

        // Boolean
        And(Vec<AppliedIdOrStar>) = "and",

        // Arithmetic
        Geq(AppliedId, AppliedId) = "geq",
        Leq(AppliedId, AppliedId) = "leq",
        Less(AppliedId, AppliedId) = "lt",
        Greater(AppliedId, AppliedId) = "gt",
        Eq(AppliedId, AppliedId) = "eq",
        Add(AppliedId, AppliedId) = "+",
        Minus(AppliedId, AppliedId) = "-",

        Number(u32),

        // (init predName syntax)
        // use to create empty compose eclass for recursive definition
        Init(AppliedId, AppliedId) = "init",
        // (interface predName syntax u32)
        // use for new predicate
        Interface(AppliedId, AppliedId, AppliedId) = "interface",
        PredName(String),
    }
}

#[derive(Default)]
pub struct CHCAnalysis;

// TODO: implement Debug to CHC clause using syn_enode
#[derive(Eq, PartialEq, Clone, Debug)]
pub struct CHCData {
    predNames: HashSet<String>,
    varTypes: HashMap<Slot, VarType>,
}

pub fn aggregateVarType(sh: &CHC, eg: &CHCEGraph) -> HashMap<Slot, VarType> {
    // debug!("aggregateVarType");
    let sh = transformToEgraphNameSpace(sh, eg);
    let mut slots = sh.slots();
    let appIds = sh.applied_id_occurrences();
    let mut varTypes = HashMap::default();
    // debug!("slots: {:?}", slots);
    for s in slots {
        for app in &appIds {
            let appInverse = app.m.inverse();
            if let Some(mapToS) = appInverse.get(s) {
                let childEclass = eg.analysis_data(app.id);
                let childSlotType = childEclass.varTypes.get(&mapToS).unwrap();
                varTypes
                    .entry(s)
                    .and_modify(|vt: &mut VarType| assert!(vt == childSlotType))
                    .or_insert(childSlotType.clone());
            }
        }
    }

    // debug!("aggregateVarType for {:?}", sh);
    // debug!("get {:?}", varTypes);

    varTypes
}

// TODO bug (crash) lookup return mismatch slots number with this enode
// guess it's case where eclass interface slots is less than the enode slot
fn transformToEgraphNameSpace(sh: &CHC, eg: &CHCEGraph) -> CHC {
    if let Some(appId) = eg.lookup(sh) {
        return eg.getExactENodeInEGraph(sh);
    }

    sh.clone()
}

fn CHCDataForPrimitiveVar(sh: &CHC, eg: &CHCEGraph, returnType: VarType) -> CHCData {
    let sh = transformToEgraphNameSpace(sh, eg);
    let mut hm = HashMap::default();
    hm.insert(*sh.slots().iter().next().unwrap(), returnType);
    debug!("result {hm:?}");
    CHCData {
        predNames: HashSet::default(),
        varTypes: hm,
    }
}

// TODO2: varType not propagate up
// TODO: internal var for each eclass
impl Analysis<CHC> for CHCAnalysis {
    type Data = CHCData;

    fn merge(x: CHCData, y: CHCData, i: Id, eg: &CHCEGraph) -> CHCData {
        let c = eg.eclass(i).unwrap();
        // debug!("calling merge to {:?}", i);
        // debug!("dump from merge c {}", c);
        // debug!("x {x:?}");
        // debug!("y {y:?}");
        // debug!("eclass {:?}", eg.eclass(i).unwrap());

        let mut newPredNames = HashSet::<String>::default();
        let xLen = x.predNames.len();
        let yLen = y.predNames.len();
        newPredNames.extend(y.predNames);
        newPredNames.extend(x.predNames);

        let mut newVarTypes = x.varTypes.clone();
        for (var, yVarType) in y.varTypes {
            if let Some(thisType) = newVarTypes.get(&var) {
                assert!(yVarType == *thisType);
            } else {
                newVarTypes.insert(var, yVarType);
            }
        }

        let eclassSlots = eg.allSlots(i);
        // debug!("eclassSlots {:?}", eclassSlots);
        let newVarTypes = newVarTypes
            .into_iter()
            .filter(|(s, vt)| eclassSlots.contains(&s))
            .collect();

        // debug!("result varTypes {:?}", newVarTypes);

        CHCData {
            predNames: newPredNames,
            varTypes: newVarTypes,
        }
    }

    fn make(eg: &CHCEGraph, sh: &CHC) -> CHCData {
        // debug!("calling make on {:?}", sh);
        match sh {
            CHC::Init(predNameId, predSyntaxId) | CHC::Interface(predNameId, predSyntaxId, _) => {
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
                }
            }
            CHC::Int(_) => CHCDataForPrimitiveVar(sh, eg, VarType::Int),
            CHC::Node(_) => CHCDataForPrimitiveVar(sh, eg, VarType::Node),
            CHC::Var(_) => CHCDataForPrimitiveVar(sh, eg, VarType::Unknown),
            _ => CHCData {
                predNames: HashSet::default(),
                varTypes: aggregateVarType(sh, eg),
            },
        }
    }

    fn modify(eg: &mut EGraph<CHC, Self>, i: Id) {}
}

pub fn dumpCHCEClass(
    i: Id,
    map: &mut HashMap<AppliedId, RecExpr<CHC>, rustc_hash::FxBuildHasher>,
    eg: &CHCEGraph,
) {
    let nodes = eg.enodes(i);
    if nodes.len() == 0 {
        return;
    }

    let mut slot_order: Vec<Slot> = eg.slots(i).into();
    slot_order.sort();
    let slot_str = slot_order
        .iter()
        .map(|x| x.to_string())
        .collect::<Vec<_>>()
        .join(", ");

    let synExpr = eg.getSynExpr(&i, map);
    print!("\n{}", synExpr);
    print!("\n{:?}", eg.analysis_data(i));
    print!("\n{:?}({}):", i, &slot_str);
    print!(">> {:?}\n", eg.getSynNodeNoSubst(&i));

    for node in eg.enodes(i) {
        print!(" - {node:?}\n");
        let (sh, m) = node.weak_shape();
        print!(" -   {sh:?}\n");
    }
    let permute = eg.getSlotPermutation(&i);
    for p in permute {
        print!(" -- {:?}\n", p);
    }
}

pub fn dumpCHCEGraph(eg: &CHCEGraph) {
    print!("\n == Egraph ==");
    let mut eclasses = eg.ids();
    eclasses.sort();

    let mut map = HashMap::<AppliedId, RecExpr<CHC>, rustc_hash::FxBuildHasher>::default();
    for i in eclasses {
        dumpCHCEClass(i, &mut map, eg);
    }
    print!("");
}

pub fn id<L: Language, N: Analysis<L>>(s: &str, eg: &mut EGraph<L, N>) -> AppliedId {
    eg.check();
    let re = RecExpr::parse(s).unwrap();
    let out = eg.add_syn_expr(re.clone());
    eg.check();
    out
}

pub fn merge(s1: &str, s2: &str, eg: &mut CHCEGraph) {
    let id1 = &id(&s1, eg);
    let id2 = &id(&s2, eg);
    eg.union(id1, id2);
}

pub fn starPVar(starIndex: u32, starCount: u32) -> String {
    format!("star_{}_{}", starIndex, starCount)
}

// get a string of star_i_j from the subst
pub fn starPStr(starIndex: u32, subst: &Subst) -> String {
    let mut res: Vec<String> = starPVecStr(starIndex, subst);
    for s in &mut res {
        s.insert_str(0, "?");
    }
    res.join(" ")
}

// get a vector of string of star_i_j from the subst
fn starPVecStr(starIndex: u32, subst: &Subst) -> Vec<String> {
    let mut countStar = 0;
    let mut allStarStr: Vec<String> = vec![];
    while subst.contains_key(&starPVar(starIndex, countStar)) {
        allStarStr.push((format!("{}", starPVar(starIndex, countStar))));
        countStar += 1;
    }
    allStarStr
}

// get all appliedId that is
pub fn starIds(starIndex: u32, subst: &Subst) -> Vec<AppliedId> {
    let mut allIds = vec![];
    let mut starCount = 0;
    // cannot merge this into one call because starCount gets updated
    while subst.contains_key(&starPVar(starIndex, starCount)) {
        allIds.push(subst[&starPVar(starIndex, starCount)].clone());
        starCount += 1;
    }

    allIds
}

pub fn starStrSortedByAppIds(starIndices: &[u32], subst: &Subst) -> String {
    let mut starStrs = vec![];
    for i in starIndices {
        starStrs.extend(starPVecStr(*i, subst));
    }
    starStrs.sort_by(|si, sj| subst[si].cmp(&subst[sj]));
    starStrs.iter_mut().for_each(|s| s.insert_str(0, "?"));
    starStrs.join(" ")
}

pub fn getMaxStarCount(starIndex: u32, subst: &Subst) -> u32 {
    let mut starMax = 0;
    while subst.contains_key(&starPVar(starIndex, starMax)) {
        starMax += 1;
    }

    starMax
}

use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;
use tracing_subscriber::filter::combinator::And;
use union_find::{QuickUnionUf, UnionBySize, UnionFind};

static G_COUNTER: AtomicUsize = AtomicUsize::new(0);

use std::collections::HashSet;

// fn unfold() -> CHCRewrite {
//     let rootPat =
//         Pattern::parse("(compose <(new ?syntax1 (and <*0>) <(compose <*1>) *2> ) *3>)").unwrap();
//     let rootPat2 = rootPat.clone();

//     let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<Subst> { ematch_all(eg, &rootPat) });
//     let applier = Box::new(
//         // (compose <[(new ?syntax2 (true) <*4>) \dot (#matches of *1)] *3>)
//         move |substs: Vec<Subst>, eg: &mut CHCEGraph| {
//             debug!("unfold rule, found {:#?}", substs);
//             for subst in substs {
//                 let star1Max = getMaxStarCount(1, &subst);

//                 let mut matches: Vec<Vec<AppliedId>> = vec![];
//                 let subPat = Pattern::parse("(new ?syntax2 (and <*6>) <*4>)").unwrap();

//                 let rootUnfoldPattern =
//                     Pattern::parse("(new ?syntax1 (and <*0>) <(compose <*1>) *2> )").unwrap();
//                 let rootClause = pattern_subst(eg, &rootUnfoldPattern, &subst);
//                 let rootUnfold =
//                     pattern_subst(eg, &Pattern::parse("(compose <*1>)").unwrap(), &subst);

//                 let rootUnfoldEnode: &CHC =
//                     &constructENodefromPatternSubst(eg, &rootUnfoldPattern, &subst).unwrap();

//                 for star1Count in 0..star1Max {
//                     let var = &starPVar(1, star1Count);
//                     let result: Vec<Subst> =
//                         ematchAllInEclass(eg, &subPat, subst[var].id, &subst[var].m);
//                     debug!("subPat = {subPat:?}");
//                     debug!("subEclass match result {result:#?}");
//                     let mut thisNewIds: Vec<AppliedId> = vec![];

//                     for mut r in result {
//                         mergeSubst(&mut r, &subst);

//                         // TODO: add interface for these new Enode
//                         let newENodePat = &format!(
//                             "(new ?syntax1 (and <{}>) <{}>)",
//                             starStrSortedByAppIds(&[0, 6], &subst),
//                             starStrSortedByAppIds(&[2, 4], &subst),
//                         );
//                         // add enode to egraph
//                         let newId = patternSubstStr(eg, newENodePat, &r);

//                         debug!(
//                             "Unfolding at {rootUnfold}, starCount {star1Count} \n {:?} \n with {:?} \n to {:?}",
//                             eg.getExactENodeInEGraph(rootUnfoldEnode),
//                             &constructENodefromPatternSubst(eg, &subPat, &r).unwrap().weak_shape().0,
//                             eg.getExactENodeInEGraph(
//                                 &constructENodefromPatternSubst(
//                                     eg,
//                                     &Pattern::parse(newENodePat).unwrap(),
//                                     &r
//                                 )
//                                 .unwrap()
//                             )
//                         );

//                         eg.analysis_data_mut(newId.id).predNames.insert(format!(
//                             "unfold_{rootUnfold}_using_{}_in_{rootClause}",
//                             subst[var].id
//                         ));
//                         thisNewIds.push(newId);
//                     }
//                     matches.push(thisNewIds);
//                 }

//                 let matchesCombination: Vec<Vec<AppliedId>> = combination(matches);
//                 let newEnode =
//                     Pattern::parse(&format!("(compose <{} *5>)", starPStr(3, &subst))).unwrap();
//                 for m in matchesCombination {
//                     assert!(m.len() == star1Max as usize);
//                     // Create a new compose Enode whose children is the vector of AppliedId and union it with the original Compose
//                     let mut newSubst = subst.clone();
//                     let mut star4Count = 0;
//                     for id in m {
//                         let key = starPVar(5, star4Count);
//                         assert!(!newSubst.contains_key(&key));
//                         newSubst.insert(key, id);
//                         star4Count += 1;
//                     }

//                     eg.union_instantiations(
//                         &rootPat2,
//                         &newEnode,
//                         &newSubst,
//                         Some("Unfold".to_string()),
//                     );
//                 }
//             }
//         },
//     );
//     RewriteT {
//         name: "unfold".to_owned(),
//         searcher: searcher,
//         applier: applier,
//     }
//     .into()
// }

fn getAnyAndChildren(appId: &AppliedId, eg: &CHCEGraph) -> Vec<AppliedIdOrStar> {
    let n = eg.enodes_applied(appId).first().unwrap().clone();
    if let CHC::And(andChildren) = n {
        return andChildren;
    };

    if let CHC::True() = n {
        return vec![];
    };

    panic!();
}

type UnfoldRecipe = (
    AppliedId,
    Vec<AppliedIdOrStar>,
    Vec<AppliedIdOrStar>,
    AppliedId,
);

#[derive(Debug)]
struct ComposeUnfoldRecipe {
    unfoldRecipe: Vec<Vec<UnfoldRecipe>>,
    exclude: usize,
    compose1Children: Vec<AppliedId>,
    rootId: AppliedId,
    compose2Id: AppliedId,
    new1EClass: AppliedId,
}

fn unfold() -> CHCRewrite {
    let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<ComposeUnfoldRecipe> {
        let rootPat = Pattern::parse("(compose <*0>)").unwrap();
        let rootMatches = ematch_all(eg, &rootPat);
        // (compose1 <(new1 syntax1 cond1 <(compose2 <new2 syntax2>)>)>)
        let mut composeUnfoldReceipt = vec![];
        for compose1Children in rootMatches {
            let rootId = lookupPattern(eg, &rootPat, &compose1Children).unwrap();
            let mut compose1Children: Vec<AppliedId> = compose1Children
                .iter()
                .map(|(s, appId)| appId.clone())
                .collect();
            compose1Children.sort();
            // TODO: it's not good to iterate while updating egraph
            for (i1, new1EClass) in compose1Children.iter().enumerate() {
                for new1 in eg.enodes_applied(new1EClass) {
                    if let CHC::Interface(..) = new1 {
                        continue;
                    }

                    let CHC::New(syntax1, cond1, new1Children) = new1 else {
                        panic!();
                    };

                    // TODO: this will only pick the first and out
                    debug!("cond1 EClass {:?}", eg.eclass(cond1.id));
                    let and1Children = getAnyAndChildren(&cond1, eg);

                    for (i2, compose2Id) in new1Children.iter().enumerate() {
                        let compose2Id = compose2Id.getAppliedId();

                        for compose2 in eg.enodes_applied(&compose2Id) {
                            if let CHC::Init(..) = compose2 {
                                continue;
                            }

                            let CHC::Compose(compose2Children) = compose2 else {
                                panic!();
                            };

                            let mut unfoldedENodesRecipe: Vec<Vec<UnfoldRecipe>> = vec![];
                            for new2EClass in compose2Children.iter() {
                                let new2EClass = new2EClass.getAppliedId();
                                let mut fromThisEClassRecipe: Vec<UnfoldRecipe> = vec![];
                                for new2 in eg.enodes_applied(&new2EClass) {
                                    if let CHC::Interface(..) = new2 {
                                        continue;
                                    }

                                    let CHC::New(syntax2, cond2, new2Children) = new2 else {
                                        panic!();
                                    };

                                    let and2Children = getAnyAndChildren(&cond2, eg);

                                    let mut unfoldedChildren = new1Children.clone();
                                    unfoldedChildren.remove(i2);
                                    // 2
                                    unfoldedChildren.extend(new2Children.clone());

                                    let mut mergeAndChildren = and1Children.clone();
                                    mergeAndChildren.extend(and2Children);

                                    fromThisEClassRecipe.push((
                                        syntax1.clone(),
                                        mergeAndChildren,
                                        unfoldedChildren,
                                        new2EClass.clone(),
                                    ));
                                }
                                unfoldedENodesRecipe.push(fromThisEClassRecipe);
                            }

                            composeUnfoldReceipt.push(ComposeUnfoldRecipe {
                                unfoldRecipe: unfoldedENodesRecipe,
                                exclude: i1,
                                compose1Children: compose1Children.clone(),
                                rootId: rootId.clone(),
                                compose2Id: compose2Id.clone(),
                                new1EClass: new1EClass.clone(),
                            });
                        }
                    }
                }
            }
        }

        composeUnfoldReceipt
    });
    let applier = Box::new(
        move |composeRecipes: Vec<ComposeUnfoldRecipe>, eg: &mut CHCEGraph| {
            let mut unfoldTotalAdd = 0;
            for composeRecipe in &composeRecipes {
                let ComposeUnfoldRecipe {
                    unfoldRecipe,
                    exclude,
                    compose1Children,
                    rootId,
                    compose2Id,
                    new1EClass,
                } = composeRecipe;
                for unfoldRecipeComb in combination(unfoldRecipe.clone()) {
                    unfoldTotalAdd += 1;
                }
            }

            debug!("expect unfold to add and union {unfoldTotalAdd} times");
            let mut countdown = unfoldTotalAdd;
            for composeRecipe in composeRecipes {
                let ComposeUnfoldRecipe {
                    unfoldRecipe,
                    exclude,
                    compose1Children,
                    rootId,
                    compose2Id,
                    new1EClass,
                } = composeRecipe;
                let mut toBeUnion = vec![];
                // this loops takes a long time, around 1sec per iter
                for unfoldRecipeComb in combination(unfoldRecipe) {
                    let mut childrenComb = vec![];
                    let start = Instant::now(); // Record the start time
                                                // this one takes around half the time of the whole loop
                    let (_, time1) = time(|| {
                        for (syntax1, mergeAndChildren, unfoldedChildren, new2EClass) in
                            unfoldRecipeComb
                        {
                            let mergeAnd = eg.add(CHC::And(mergeAndChildren));
                            let unfoldedENode = CHC::New(syntax1, mergeAnd, unfoldedChildren);
                            let unfoldedENodeId = eg.add(unfoldedENode);
                            eg.analysis_data_mut(unfoldedENodeId.id)
                                .predNames
                                .insert(format!(
                                    "unfold_{compose2Id}_in_{new1EClass}_using_{new2EClass}"
                                ));
                            childrenComb.push(unfoldedENodeId);
                        }
                    });

                    let (_, time2) = time(|| {
                        let mut unfoldedComposeChildren = compose1Children.clone();
                        unfoldedComposeChildren.remove(exclude);
                        unfoldedComposeChildren.extend(childrenComb);
                        let unfoldedComposeChildren = unfoldedComposeChildren
                            .into_iter()
                            .map(|appId| AppliedIdOrStar::AppliedId(appId.clone()))
                            .collect();
                        let unfoldedCompose = eg.add(CHC::Compose(unfoldedComposeChildren));
                        toBeUnion.push(unfoldedCompose);
                        countdown -= 1;
                        debug!("unfold countdown {countdown}");
                        debug!(
                            "egraph enodes {} eclasses {}",
                            eg.total_number_of_nodes(),
                            eg.totalNumberOfEclass()
                        );
                    });

                    // time1 takes 2x to 4x the time of time2
                    debug!("time1 {time1:?}");
                    debug!("time2 {time2:?}");
                }
                let mut totalENodes = 0;
                totalENodes += eg.enodes(rootId.id).len();
                for x in &toBeUnion {
                    totalENodes += eg.enodes(x.id).len();
                }
                debug!("toBeUnion size {}", toBeUnion.len());
                debug!("after union, total {totalENodes} enodes");
                // if there's no union here, it ends very fast
                for x in toBeUnion {
                    eg.union(&rootId, &x);
                }
            }
        },
    );
    RewriteT {
        name: "unfold".to_owned(),
        searcher: searcher,
        applier: applier,
    }
    .into()
}

// fn newChildrenPermute() -> CHCRewrite {
//     let pat = Pattern::parse("(new ?syntax ?cond <*1>)").unwrap();
//     let patClone = pat.clone();
//     let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<Subst> { ematch_all(eg, &patClone) });
//     let applier = Box::new(move |substs: Vec<Subst>, eg: &mut CHCEGraph| {
//         // TODO: is there a different between using AppliedId and Id
//         let mut did = HashSet::<(AppliedId, AppliedId, BTreeSet<AppliedId>)>::default();
//         let newPat = Pattern::parse("(new ?syntax ?cond <*2>)").unwrap();
//         for subst in substs {
//             let mut thisDid = BTreeSet::<AppliedId>::default();
//             for (var, id) in subst.iter() {
//                 thisDid.insert(id.clone());
//             }

//             let mut this = (subst["syntax"].clone(), subst["cond"].clone(), thisDid);
//             if did.contains(&this) {
//                 continue;
//             }

//             did.insert(this);

//             // TODO: make new children follow old vars?
//             let ids = starIds(1, &subst);
//             let idsPermuts = permute(&ids);
//             let mut newSubst = subst.clone();
//             for permut in idsPermuts {
//                 let mut newSubstTmp = newSubst.clone();
//                 for (i, id) in permut.iter().enumerate() {
//                     newSubstTmp.insert(starPVar(2, i.try_into().unwrap()), id.clone());
//                 }
//                 eg.union_instantiations(
//                     &pat,
//                     &newPat,
//                     &newSubstTmp,
//                     Some("newChildrenPermute".to_string()),
//                 );
//             }
//         }
//     });
//     RewriteT {
//         name: "newPermute".to_owned(),
//         searcher,
//         applier,
//     }
//     .into()
// }

// TODO: can use marking to determine that we already permute this Enode
// fn composeChildrenPermute() -> CHCRewrite {
//     let pat = Pattern::parse("(compose <*1>)").unwrap();
//     let patClone = pat.clone();
//     let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<Subst> { ematch_all(eg, &patClone) });
//     let applier = Box::new(move |substs: Vec<Subst>, eg: &mut CHCEGraph| {
//         // TODO: is there a different between using AppliedId and Id
//         let mut did = HashSet::<BTreeSet<AppliedId>>::default();
//         let newPat = Pattern::parse("(compose <*2>)").unwrap();
//         for subst in substs {
//             let mut thisDid = BTreeSet::<AppliedId>::default();
//             for (var, id) in subst.iter() {
//                 thisDid.insert(id.clone());
//             }

//             if did.contains(&thisDid) {
//                 continue;
//             }

//             did.insert(thisDid);

//             let ids = starIds(1, &subst);
//             let idsPermuts = permute(&ids);
//             let mut newSubst = subst.clone();
//             for permut in idsPermuts {
//                 let mut newSubstTmp = newSubst.clone();
//                 for (i, id) in permut.iter().enumerate() {
//                     newSubstTmp.insert(starPVar(2, i.try_into().unwrap()), id.clone());
//                 }
//                 eg.union_instantiations(
//                     &pat,
//                     &newPat,
//                     &newSubstTmp,
//                     Some("composeChildrenPermute".to_string()),
//                 );
//             }
//         }
//     });
//     RewriteT {
//         name: "composePermute".to_owned(),
//         searcher,
//         applier,
//     }
//     .into()
// }

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
                .getExactENodeInEGraph(&constructENodefromPatternSubst(eg, &pat, &subst).unwrap());

            // TODO0: try change to rootData instead of mergeVarTypes
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

                let childrenVarTypes = &eg.analysis_data(appId.id).varTypes;
                debug!("childrenVarTypes = {childrenVarTypes:#?}");
                mergeVarTypes.extend(
                    appId
                        .m
                        .clone()
                        .into_iter()
                        .map(|(from, to)| (to, *childrenVarTypes.get(&from).unwrap())),
                );
            }

            // debug!("mergeVarTypes = {mergeVarTypes:#?}");
            // debug!("varToChildIndx = {varToChildIndx:#?}");

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
                let counter = G_COUNTER.load(Ordering::SeqCst);

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
                G_COUNTER.store(counter + 1, Ordering::SeqCst);

                let composeEnode = CHC::Compose(vec![AppliedIdOrStar::AppliedId(newENodeAppId)]);
                let composeAppId = eg.add(composeEnode);
                debug!("define new {:?}", composeAppId);
            }
        }
    });

    RewriteT {
        name: "define".to_owned(),
        searcher,
        applier,
    }
    .into()
}

fn trueToAnd() -> CHCRewrite {
    let pat = "(true)";
    let outPat = "(and <>)";
    Rewrite::new("trueToAnd", pat, outPat)
}

pub fn getAllRewrites() -> Vec<CHCRewrite> {
    vec![
        unfold(),
        // newChildrenPermute(),
        // composeChildrenPermute(),
        // defineFromSharingBlock(),
        trueToAnd(),
    ]
}

type CHCEGraph = EGraph<CHC, CHCAnalysis>;
type CHCRewrite = Rewrite<CHC, CHCAnalysis>;
type CHCRunner = Runner<CHC, CHCAnalysis>;

fn minDummy(x: &str, y: &str, z: &str) -> String {
    let syntax = format!("(pred <{x} {y} {z}>)");
    format!("(init min {syntax})")
}

fn minCHC(x: &str, y: &str, z: &str, eg: &mut CHCEGraph) -> AppliedId {
    let syntax = format!("(pred <{x} {y} {z}>)");
    // min(X,Y,Z) <- X< Y, Z=X
    let cond1 = format!("(and <(lt {x} {y}) (eq {z} {x})>)");
    let chc1 = format!("(new {syntax} {cond1} <>)");
    let itf1 = format!("(interface min {syntax} 1)");
    merge(&chc1, &itf1, eg);

    // min(X,Y,Z) <- X >= Y, Z=Y
    let cond2 = format!("(and <(geq {x} {y}) (eq {z} {y})>)");
    let chc2 = format!("(new {syntax} {cond2} <>)");
    let itf2 = format!("(interface min {syntax} 2)");
    merge(&chc1, &itf1, eg);

    id(&format!("(compose <{chc1} {chc2}>)"), eg)
}

fn minLeafDummy(x: &str, y: &str) -> String {
    let syntax = format!("(pred <{x} {y}>)");
    format!("(init minLeaf {syntax})")
}

fn minLeafCHC(x: &str, y: &str, count: &mut u32, eg: &mut CHCEGraph) -> AppliedId {
    let a = generateVarFromCount(count, VarType::Int);
    let l = generateVarFromCount(count, VarType::Node);
    let r = generateVarFromCount(count, VarType::Node);
    let m1 = generateVarFromCount(count, VarType::Int);
    let m2 = generateVarFromCount(count, VarType::Int);
    let m3 = generateVarFromCount(count, VarType::Int);

    let syntax = format!("(pred <{x} {y}>)");

    // min-leaf(X,Y) <- X=leaf, Y=0
    let cond1 = format!("(and <(eq {y} 0) (eq {x} (leaf))>)");
    let chc1 = format!("(new {syntax} {cond1} <>)");
    let itf1 = format!("(interface minLeaf {syntax} 1)");
    merge(&chc1, &itf1, eg);

    // min-leaf(X,Y) <- X=node(A,L,R), Y=M3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3)
    let cond2 = format!("(and <(eq {x} (binode {a} {l} {r})) (eq {y} (+ {m3} 1))>)");
    let chc2 = format!(
        "(new {syntax} {cond2} <{} {} {}>)",
        minLeafDummy(&l, &m1),
        minLeafDummy(&r, &m2),
        minDummy(&m1, &m2, &m3)
    );
    let itf2 = format!("(interface minLeaf {syntax} 2)");
    merge(&chc2, &itf2, eg);

    id(&format!("(compose <{itf1} {itf2}>)"), eg)
}

fn leafDropDummy(x: &str, y: &str, z: &str) -> String {
    let syntax = format!("(pred <{x} {y} {z}>)");
    format!("(init leafDrop {syntax})")
}

fn leafDropCHC(x: &str, y: &str, z: &str, count: &mut u32, eg: &mut CHCEGraph) -> AppliedId {
    let syntax = format!("(pred <{x} {y} {z}>)");

    // left-drop(x,y,z) ← y=leaf, z=leaf
    let cond1 = format!("(and <(eq {y} (leaf)) (eq {z} (leaf))>)");
    let chc1 = format!("(new {syntax} {cond1} <>)");
    let itf1 = format!("(interface leafDrop {syntax} 1)");
    merge(&chc1, &itf1, eg);

    // left-drop(x, y ,z) ← x ≤0, y = node(a,L,R), z = node(a,L,R)
    let l = generateVarFromCount(count, VarType::Node);
    let r = generateVarFromCount(count, VarType::Node);
    let a = generateVarFromCount(count, VarType::Int);
    let cond2 =
        format!("(and <(leq {x} 0) (eq {y} (binode {a} {l} {r})) (eq {z} (binode {a} {l} {r}))>)");
    let chc2 = format!("(new {syntax} {cond2} <>)");
    let itf2 = format!("(interface leafDrop {syntax} 2)");
    merge(&chc2, &itf2, eg);

    // left-drop(x,y,z) ← y= node(a,L,R), x ≥1,N1=x−1, left-drop(N1,L,z)
    let l1 = generateVarFromCount(count, VarType::Node);
    let r1 = generateVarFromCount(count, VarType::Node);
    let a1 = generateVarFromCount(count, VarType::Int);
    let n1 = generateVarFromCount(count, VarType::Int);
    let cond3 = format!("(and <(eq {y} (binode {a1} {l1} {r1})) (geq {x} 1) (eq {n1} (- {x} 1))>)");
    let chc3 = format!("(new {syntax} {cond3} <{}>)", leafDropDummy(x, y, z));
    let itf3 = format!("(interface leafDrop {syntax} 3)");
    merge(&chc3, &itf3, eg);

    id(&format!("(compose <{chc1} {chc2} {chc3}>)"), eg)
}

fn rootDummy(n: &str, t: &str, u: &str, m: &str, k: &str) -> String {
    let syntax = format!("(pred <{n} {t} {u} {m} {k}>)");
    format!("(init root {syntax})")
}

fn rootDummy2(n: &str, t: &str, u: &str) -> String {
    let syntax = format!("(pred <{n} {t} {u}>)");
    format!("(init root {syntax})")
}

fn addPredName(id: Id, predName: String, eg: &mut CHCEGraph) {
    let data = eg.analysis_data_mut(id);
    data.predNames.insert(predName);
}

fn tst2() {
    // TODO: how to determine slot type?
    initLogger();
    let mut egOrig = CHCEGraph::default();
    let mut count = 0;
    {
        let eg = &mut egOrig;

        let n = &generateVarFromCount(&mut count, VarType::Int);
        let t = &generateVarFromCount(&mut count, VarType::Node);
        let u = &generateVarFromCount(&mut count, VarType::Node);
        let m = &generateVarFromCount(&mut count, VarType::Int);
        let k = &generateVarFromCount(&mut count, VarType::Int);

        //  false ← N≥0,M+N<K, left-drop(N,T,U), min-leaf(U,M), min-leaf(T,K)
        let syntax = "(pred <>)";
        let cond = format!("(and <(geq {n} 0) (lt (+ {m} {n}) {k})>)");
        let rootCHC: String = format!(
            "(new {syntax} {cond} <{} {} {}>)",
            leafDropDummy(n, t, u),
            minLeafDummy(u, m),
            minLeafDummy(t, k)
        );
        let composeRoot = format!("(compose <{rootCHC}>)");

        let rootDummyId = id(&rootDummy(n, t, u, m, k), eg);
        let rootId = id(&composeRoot, eg);
        eg.union(&rootId, &rootDummyId);

        let x = &generateVarFromCount(&mut count, VarType::Int);
        let y = &generateVarFromCount(&mut count, VarType::Int);
        let z = &generateVarFromCount(&mut count, VarType::Int);

        let minDummyId = id(&minDummy(x, y, z), eg);
        let minId = minCHC(x, y, z, eg);
        eg.union(&minDummyId, &minId);

        let x = &generateVarFromCount(&mut count, VarType::Int);
        let y = &generateVarFromCount(&mut count, VarType::Node);
        let z = &generateVarFromCount(&mut count, VarType::Node);

        let leafDropDummyId = id(&leafDropDummy(x, y, z), eg);
        let leafDropId = leafDropCHC(x, y, z, &mut count, eg);
        eg.union(&leafDropDummyId, &leafDropId);

        let x = &generateVarFromCount(&mut count, VarType::Node);
        let y = &generateVarFromCount(&mut count, VarType::Int);

        let minLeafDummyId = id(&minLeafDummy(x, y), eg);
        let minLeafId = minLeafCHC(x, y, &mut count, eg);
        eg.union(&minLeafDummyId, &minLeafId);

        debug!("egraph before run");
        dumpCHCEGraph(&eg);
    }

    // TODO: can we not use mem::take here?
    let mut runner: CHCRunner = Runner::default().with_egraph(egOrig).with_iter_limit(1);
    let report = runner.run(&getAllRewrites());
    debug!("report {report:?}");

    debug!("egraph after run");
    dumpCHCEGraph(&runner.egraph);

    // check unfold result
    // 19. new1(N,M,K)←M=0,K=0
    // 20. new1(N,M,K)←N≤0,M=M3+1,K=K3+1, min-leaf(L,M1), min-leaf(R,M2), min(M1,M2,M3), min-leaf(L,K1), min-leaf(R,K2), min(K1,K2,K3)
    // 21. new1(N,M,K)←N≥1,N1=N−1 K=K3+1, left-drop(N1,L,U), min-leaf(U,M), min-leaf(L,K1), min-leaf(R,K2), min(K1,K2,K3)

    let n = &generateVarFromCount(&mut count, VarType::Int);
    let m = &generateVarFromCount(&mut count, VarType::Int);
    let k = &generateVarFromCount(&mut count, VarType::Int);
    let syntax = format!("(pred <{n} {m} {k}>)");
    let cond = format!("(and <(eq {k} 0) (eq {m} 0)>)");
    // let chc: String = format!("(new {syntax} {cond} <>)");
    // let res = ematch_all(&runner.egraph, &Pattern::parse(&chc).unwrap());
    let res = ematch_all(&runner.egraph, &Pattern::parse(&cond).unwrap());
    assert!(res.len() >= 1);
}

fn main() {
    tst2();
}
