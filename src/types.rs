use crate::*;
use log::{debug, error, info, trace};
use nauty_Traces_sys::{
    densenauty, empty_graph, optionblk, statsblk, ADDONEEDGE, FALSE, SETWORDSNEEDED, TRUE,
};
use std::cell::RefCell;
#[cfg(not(feature = "parallelAdd"))]
use std::cell::{Ref, RefMut};
use std::collections::{BTreeMap, BTreeSet};
use std::os::raw::c_int;
#[cfg(feature = "parallelAdd")]
use std::sync::RwLock;
use std::sync::{RwLockReadGuard, RwLockWriteGuard};

/// Ids identify e-classes.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Id(pub usize);

/// Ids identify e-nodes.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct ENodeId(pub usize);

/// AppliedIds are invocations of e-classes.
///
/// Recall that in slotted egraphs, e-classes have arguments - and in order to talk about the set of terms in an e-class, you always need to invocate your e-class using a bunch of arguments.
/// This "invocation" is what an AppliedId represents. The [Id] part identifies an e-class, and the [SlotMap] is used to map the argument-slots of the e-class to the values that you put into them.
#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct AppliedId {
    pub id: Id,

    // m is always a bijection!
    // m maps the slots from `id` (be it ENode::slots() in a RecExpr, or EGraph::slots(Id) for eclasses) to the slots that we insert into it.
    // m.keys() == id.slots
    pub m: SlotMap,
}

#[derive(Clone, Hash, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub enum AppliedIdOrStar {
    AppliedId(AppliedId),
    Star(u32),
}

impl AppliedIdOrStar {
    pub fn getAppliedId(&self) -> AppliedId {
        let AppliedIdOrStar::AppliedId(appId) = self else {
            panic!();
        };

        appId.clone()
    }

    pub fn getAppliedIdOwn(self) -> AppliedId {
        let AppliedIdOrStar::AppliedId(appId) = self else {
            panic!();
        };

        appId
    }
}

impl From<AppliedIdOrStar> for AppliedId {
    fn from(appId: AppliedIdOrStar) -> AppliedId {
        let AppliedIdOrStar::AppliedId(appId) = appId else {
            panic!();
        };

        appId.clone()
    }
}

impl From<AppliedId> for AppliedIdOrStar {
    fn from(appId: AppliedId) -> AppliedIdOrStar {
        AppliedIdOrStar::AppliedId(appId)
    }
}

pub fn toAppliedIdOrStarVec(appId: Vec<AppliedId>) -> Vec<AppliedIdOrStar> {
    appId.into_iter().map(AppliedIdOrStar::AppliedId).collect()
}

/// A "term" or "expression" from some given [Language] L.
// The AppliedIds in `node` are ignored (any typically set to AppliedId::null()). They are replaced by the children RecExpr.
// A non-fancy version of RecExpr that uses the slots as "names".
#[derive(Clone, PartialEq, Eq)]
pub struct RecExpr<L: Language> {
    pub node: L,
    pub children: Vec<RecExpr<L>>,
}

impl AppliedId {
    pub fn new(id: Id, m: SlotMap) -> Self {
        let s = AppliedId { id, m };
        if CHECKS {
            s.check();
        }
        s
    }

    pub(crate) fn check(&self) {
        if !self.m.is_bijection() {
            error!("self {self:#?}");
        }
        assert!(self.m.is_bijection());
    }

    #[track_caller]
    pub fn apply_slotmap(&self, m: &SlotMap) -> AppliedId {
        if CHECKS {
            assert!(
                m.keys_set().is_superset(&self.slots()),
                "AppliedId::apply_slotmap: The SlotMap doesn't map all free slots! map {:#?} vs {:#?}",
                m,
                self.slots()
            );
        }
        self.apply_slotmap_intersect(m)
    }

    pub fn apply_slotmapMut(&mut self, m: &SlotMap) {
        if CHECKS {
            assert!(
                m.keys_set().is_superset(&self.slots()),
                "AppliedId::apply_slotmap: The SlotMap doesn't map all free slots! map {:#?} vs {:#?}",
                m,
                self.slots()
            );
        }
        self.apply_slotmap_intersectMut(m)
    }

    pub fn apply_slotmap_intersect(&self, m: &SlotMap) -> AppliedId {
        AppliedId::new(self.id, self.m.compose_intersect(m))
    }

    pub fn apply_slotmap_intersectMut(&mut self, m: &SlotMap) {
        self.m.compose_intersectMut(m);
    }

    pub fn applySlotMapPartial(&self, m: &SlotMap) -> AppliedId {
        AppliedId::new(self.id, self.m.composePartial(m))
    }

    pub fn apply_slotmap_fresh(&self, m: &SlotMap) -> AppliedId {
        AppliedId::new(self.id, self.m.compose_fresh(m))
    }

    pub fn key_slots(&self) -> SmallHashSet<Slot> {
        self.m.keys_set()
    }

    pub fn slots(&self) -> SmallHashSet<Slot> {
        self.m.values_set()
    }

    // ordered!
    pub fn slots_mut(&mut self) -> Vec<&mut Slot> {
        self.m.values_mut().collect()
    }

    pub fn null() -> Self {
        AppliedId {
            id: Id(0),
            m: SlotMap::new(),
        }
    }

    pub fn fullDump(&self) {
        println!("{:?}: {:?}", self.id, self.m)
    }
}

// TODO: assert that appIds vec is initialized in weak shape
fn renameAppIdsAndPerms(
    appIdsVec: &Vec<&AppliedId>,
    allPerms: Option<&Vec<Vec<ProvenPerm>>>,
) -> (
    Vec<AppliedId>,
    Option<Vec<Vec<ProvenPerm>>>,
    BTreeMap<Id, Id>,
    BTreeMap<Id, SlotMap>,
) {
    let mut slotMaps: BTreeMap<Id, SlotMap> = BTreeMap::new();

    let mut idMap: BTreeMap<Id, Id> = BTreeMap::new();
    {
        let mut appIdsVecSort = appIdsVec.clone();
        appIdsVecSort.sort();
        for appId in appIdsVecSort.iter() {
            let idMapLen = Id(idMap.len());
            idMap.entry(appId.id).or_insert(idMapLen);
        }
    }

    let mut newAppIds = vec![];
    for appId in appIdsVec.iter() {
        let newId = *idMap.get(&appId.id).unwrap();

        let mut updatedMap = SlotMap::new();
        let mut slotMap = SlotMap::new();
        for (i, (from, to)) in appId.m.iter().enumerate() {
            // assert!(to < appId.m.len());
            let newSlot = Slot::numeric(i as u32);
            slotMap.insert(from, newSlot);
            updatedMap.insert(newSlot, to);
        }
        slotMaps.insert(appId.id, slotMap);
        newAppIds.push(AppliedId {
            id: newId,
            m: updatedMap,
        });
    }

    let newAllPerms = if let Some(allPerms) = allPerms {
        let mut newAllPerms: Vec<Vec<ProvenPerm>> = vec![];
        for (i, perms) in allPerms.iter().enumerate() {
            let mut newPerms: Vec<ProvenPerm> = vec![];
            let id = appIdsVec[i].id;
            for perm in perms.iter() {
                let mut newPerm: Perm = SlotMap::new();
                for (from, to) in perm.iter() {
                    let newFrom = slotMaps[&id].get(from).unwrap();
                    let newTo = slotMaps[&id].get(to).unwrap();
                    newPerm.insert(newFrom, newTo);
                }
                newPerms.push(ProvenPerm { elem: newPerm });
            }
            newAllPerms.push(newPerms);
        }
        Some(newAllPerms)
    } else {
        None
    };

    (newAppIds, newAllPerms, idMap, slotMaps)
}

// TODO: create a caching from weak shape of appIdsVec with perm to result
// we can rename ids e.g. id357, id392, id394, id410 -> id0, id1, id2, id3 as long as the ids remain sorted
// we can also rename slots e.g. f10654, f10655, f10656, f10657 -> 0, 1, 2, 3
// this way we have more chance to reuse the result
pub fn canonAppIdsOrig<'a>(
    appIdsVec: &'a Vec<AppliedId>,
    allPerms: Option<&Vec<Vec<ProvenPerm>>>,
) -> (Vec<i32>, Vec<(&'a AppliedId, usize)>, BTreeMap<Slot, usize>) {
    if appIdsVec.len() == 0 {
        return (vec![], vec![], BTreeMap::new());
    }

    // {f(x, y), f(y, x), g(x, y)}
    // should have a color order f < g < arg < var
    // 1(f) - 2(arg) - 3(arg)
    // 4(f) - 5(arg) - 6(arg)
    // 7(g) - 8(arg) - 9(arg)
    // x - 10(var)
    // y - 11(var)
    // 2(arg) - 10(var)
    // 5(arg) - 11(var)
    // 3(arg) - 11(var)
    // 6(arg) - 10(var)
    // 8(arg) - 10(var)
    // 9(arg) - 11(var)

    // TODO: remove this
    // let (labAlt, appIdToVAlt, slotsToVAlt) = canonAppIdsWithRename(appIdsVec, allPerms);

    // trace!("canonAppIds appIdsVec {appIdsVec:?}");
    // trace!("allPerms {allPerms:?}");

    let mut totalV = 0;
    // total number of vertices = sum (1 + nums_function_args) + nums_variables
    let mut allSlots: BTreeSet<Slot> = BTreeSet::new();
    // must be vec because there might be duplicates
    let mut appIdToV = Vec::new();
    let mut argsV = vec![];
    // vertex for each function + its argument position
    for child in appIdsVec.iter() {
        appIdToV.push((child, totalV));
        for i in 0..child.len() {
            argsV.push(totalV + i + 1);
        }
        totalV += 1 + child.len();
        allSlots.extend(child.public_slot_occurrences_iter());
    }

    // vertex for each slot
    let mut slotsToV = BTreeMap::new();
    for s in allSlots {
        slotsToV.insert(s, totalV);
        totalV += 1;
    }

    let m = SETWORDSNEEDED(totalV);
    let mut g = empty_graph(m, totalV);

    // add edges
    let mut curr = 0;
    for (_i, child) in appIdsVec.iter().enumerate() {
        // 1(f) - 2(arg) - 3(arg)

        if child.len() > 0 {
            // 1(f) - 2(arg)
            ADDONEEDGE(&mut g, curr, curr + 1, m);
            // println!("edge {curr} {}", curr + 1);
        }

        curr += 1;
        // if there's no children, this will move to the new appId automatically

        // 2(arg) - 3(arg)
        for (i, s) in child.public_slot_occurrences_iter().enumerate() {
            if i != child.len() - 1 {
                ADDONEEDGE(&mut g, curr, curr + 1, m);
                // println!("edge {curr} {}", curr + 1);
            }

            // 2(arg) - 10(var)
            ADDONEEDGE(&mut g, curr, slotsToV[&s], m);
            curr += 1;
        }
    }

    if allPerms.is_some() {
        let allPerms = allPerms.as_ref().unwrap();
        assert!(allPerms.len() == appIdToV.len());
        for (i, perms) in allPerms.iter().enumerate() {
            let startArgsV = appIdToV[i].1 + 1;
            for p in perms {
                let newArgs = p.elem.composePartial(&appIdsVec[i].m);
                for (j, s) in newArgs.values_immut().enumerate() {
                    ADDONEEDGE(&mut g, startArgsV + j, slotsToV[s], m);
                }
            }
        }
    }

    // color sorted by eclass id then follow by args and vars
    let mut appIdToVVec = appIdToV
        .iter()
        .map(|(x, v)| (x.id(), v))
        .collect::<Vec<_>>();
    // sort by id
    appIdToVVec.sort();
    let mut lab: Vec<i32> = vec![];
    let mut ptn = vec![];

    // color for ids
    let mut groupLen = 0;
    let mut thisGroupId = appIdToVVec[0].0;
    for (id, v) in &appIdToVVec {
        lab.push(**v as i32);
        if *id == thisGroupId {
            groupLen += 1;
        } else {
            for _ in 0..groupLen - 1 {
                ptn.push(1);
            }
            ptn.push(0);

            groupLen = 1;
            thisGroupId = *id;
        }
    }
    assert!(groupLen > 0);
    for _ in 0..groupLen - 1 {
        ptn.push(1);
    }
    ptn.push(0);
    // println!("currLabLen after ids color {}", lab.len());

    // color for args
    if argsV.len() > 0 {
        lab.extend(argsV.iter().map(|i| *i as i32));
        for _ in 0..argsV.len() - 1 {
            ptn.push(1);
        }
        ptn.push(0);
    }

    // color for vars
    let currLabLen = lab.len();
    for i in currLabLen..totalV {
        lab.push(i as i32);
    }

    assert_eq!(totalV - currLabLen, slotsToV.len());
    if slotsToV.len() > 0 {
        for _ in 0..slotsToV.len() - 1 {
            ptn.push(1);
        }
        ptn.push(0);
    }

    // output structures
    let mut orbits = vec![0; totalV];
    let mut canonG = empty_graph(m, totalV);
    let mut stats = statsblk::default();

    let mut options = optionblk::default();
    options.getcanon = TRUE; // Compute canonical labeling
    options.defaultptn = FALSE; // Use custom lab and ptn for colors

    assert_eq!(lab.len(), totalV);
    assert_eq!(ptn.len(), totalV);
    assert!(g.len() == (m * totalV));
    assert!(canonG.len() == (m * totalV));
    assert!(*lab.iter().max().unwrap() == (totalV - 1) as i32);

    unsafe {
        densenauty(
            g.as_mut_ptr(),
            lab.as_mut_ptr(),
            // if ptn[i] = 0, then a group (colour class) ends at position i
            ptn.as_mut_ptr(),
            orbits.as_mut_ptr(),
            &mut options,
            &mut stats,
            m as c_int,
            totalV as c_int,
            canonG.as_mut_ptr(),
        );
    }

    // the value of lab on return is the canonical labelling
    // of the graph. Precisely, it lists the vertices of g in the order in which they need to
    // be relabelled to give canong
    trace!("appIdsVec {appIdsVec:?}");
    trace!("lab {lab:?}");

    // assert_eq!(lab, labAlt);
    // assert_eq!(
    //     appIdToV
    //         .iter()
    //         .map(|(x, v): &(&AppliedId, usize)| ((**x).clone(), *v))
    //         .collect::<Vec<(AppliedId, usize)>>(),
    //     appIdToVAlt
    // );
    // assert_eq!(slotsToV, slotsToVAlt);
    (lab, appIdToV, slotsToV)
}

fn translateBack(
    appIdToV: &Vec<(AppliedId, usize)>,
    idMap: &BTreeMap<Id, Id>,
    slotMaps: &BTreeMap<Id, SlotMap>,
) -> Vec<(AppliedId, usize)> {
    let idMapInverse: BTreeMap<Id, Id> = idMap.iter().map(|(k, v)| (*v, *k)).collect();
    appIdToV
        .iter()
        .map(|(appId, v)| {
            let origId = *idMapInverse.get(&appId.id).unwrap();
            let slotMapInverse = slotMaps.get(&origId).unwrap().inverse();
            (
                AppliedId {
                    id: origId,
                    m: appId
                        .m
                        .iter()
                        .map(|(from, to)| {
                            (
                                slotMapInverse
                                    .get(from)
                                    .expect(&format!("{from} not found")),
                                to,
                            )
                        })
                        .collect(),
                },
                *v,
            )
        })
        .collect()
}

#[cfg(not(feature = "parallelAdd"))]
#[derive(Default)]
pub struct CanonAppIdsCache {
    cache: RefCell<
        BTreeMap<
            (Vec<AppliedId>, Option<Vec<Vec<ProvenPerm>>>),
            (Vec<i32>, Vec<(AppliedId, usize)>, BTreeMap<Slot, usize>),
        >,
    >,
    pub hits: RefCell<usize>,
    pub misses: RefCell<usize>,
}

pub type CanonAppIdsCacheValue = (Vec<i32>, Vec<(AppliedId, usize)>, BTreeMap<Slot, usize>);
pub type CanonAppIdsCacheKey = (Vec<AppliedId>, Option<Vec<Vec<ProvenPerm>>>);

#[cfg(feature = "parallelAdd")]
#[derive(Default)]
pub struct CanonAppIdsCache {
    cache: RwLock<BTreeMap<CanonAppIdsCacheKey, CanonAppIdsCacheValue>>,
    pub hits: RwLock<usize>,
    pub misses: RwLock<usize>,
}

impl CanonAppIdsCache {
    #[cfg(feature = "parallelAdd")]
    pub fn getCache(
        &self,
    ) -> RwLockReadGuard<
        BTreeMap<
            (Vec<AppliedId>, Option<Vec<Vec<ProvenPerm>>>),
            (Vec<i32>, Vec<(AppliedId, usize)>, BTreeMap<Slot, usize>),
        >,
    > {
        self.cache.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getCache(&self) -> Ref<BTreeMap<CanonAppIdsCacheKey, CanonAppIdsCacheValue>> {
        self.cache.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getCacheMut(
        &self,
    ) -> RwLockWriteGuard<BTreeMap<CanonAppIdsCacheKey, CanonAppIdsCacheValue>> {
        self.cache.write().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getCacheMut(&self) -> RefMut<BTreeMap<CanonAppIdsCacheKey, CanonAppIdsCacheValue>> {
        self.cache.borrow_mut()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getHits(&self) -> RwLockReadGuard<usize> {
        self.hits.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getHits(&self) -> Ref<usize> {
        self.hits.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getHitsMut(&self) -> RwLockWriteGuard<usize> {
        self.hits.write().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getHitsMut(&self) -> RefMut<'_, usize> {
        self.hits.borrow_mut()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getMisses(&self) -> RwLockReadGuard<usize> {
        self.misses.read().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getMisses(&self) -> Ref<usize> {
        self.misses.borrow()
    }

    #[cfg(feature = "parallelAdd")]
    pub fn getMissesMut(&self) -> RwLockWriteGuard<usize> {
        self.misses.write().unwrap()
    }

    #[cfg(not(feature = "parallelAdd"))]
    pub fn getMissesMut(&self) -> RefMut<'_, usize> {
        self.misses.borrow_mut()
    }
}

fn canonAppIdsInternal(
    appIdsVec: &Vec<AppliedId>,
    allPerms: &Option<Vec<Vec<ProvenPerm>>>,
    cache: &CanonAppIdsCache,
) -> (Vec<i32>, Vec<(AppliedId, usize)>, BTreeMap<Slot, usize>) {
    // {f(x, y), f(y, x), g(x, y)}
    // should have a color order f < g < arg < var
    // 1(f) - 2(arg) - 3(arg)
    // 4(f) - 5(arg) - 6(arg)
    // 7(g) - 8(arg) - 9(arg)
    // x - 10(var)
    // y - 11(var)
    // 2(arg) - 10(var)
    // 5(arg) - 11(var)
    // 3(arg) - 11(var)
    // 6(arg) - 10(var)
    // 8(arg) - 10(var)
    // 9(arg) - 11(var)

    if let Some(cacheResult) = cache.getCache().get(&(appIdsVec.clone(), allPerms.clone())) {
        *cache.getHitsMut() += 1;

        return cacheResult.clone();
    }
    *cache.getMissesMut() += 1;

    trace!("canonAppIds appIdsVec {appIdsVec:?}");
    trace!("allPerms {allPerms:?}");

    let mut totalV = 0;
    // total number of vertices = sum (1 + nums_function_args) + nums_variables
    let mut allSlots: BTreeSet<Slot> = BTreeSet::new();
    // must be vec because there might be duplicates
    let mut appIdToV = Vec::new();
    let mut argsV = vec![];
    // vertex for each function + its argument position
    for child in appIdsVec.iter() {
        appIdToV.push((child, totalV));
        for i in 0..child.len() {
            argsV.push(totalV + i + 1);
        }
        totalV += 1 + child.len();
        allSlots.extend(child.public_slot_occurrences_iter());
    }

    // vertex for each slot
    let mut slotsToV = BTreeMap::new();
    for s in allSlots {
        slotsToV.insert(s, totalV);
        totalV += 1;
    }

    let m = SETWORDSNEEDED(totalV);
    let mut g = empty_graph(m, totalV);

    // add edges
    let mut curr = 0;
    for (_i, child) in appIdsVec.iter().enumerate() {
        // 1(f) - 2(arg) - 3(arg)

        if child.len() > 0 {
            // 1(f) - 2(arg)
            ADDONEEDGE(&mut g, curr, curr + 1, m);
            // println!("edge {curr} {}", curr + 1);
        }

        curr += 1;
        // if there's no children, this will move to the new appId automatically

        // 2(arg) - 3(arg)
        for (i, s) in child.public_slot_occurrences_iter().enumerate() {
            if i != child.len() - 1 {
                ADDONEEDGE(&mut g, curr, curr + 1, m);
                // println!("edge {curr} {}", curr + 1);
            }

            // 2(arg) - 10(var)
            ADDONEEDGE(&mut g, curr, slotsToV[&s], m);
            curr += 1;
        }
    }

    if allPerms.is_some() {
        let allPerms = allPerms.as_ref().unwrap();
        assert!(allPerms.len() == appIdToV.len());
        for (i, perms) in allPerms.iter().enumerate() {
            let startArgsV = appIdToV[i].1 + 1;
            for p in perms {
                let newArgs = p.elem.composePartial(&appIdsVec[i].m);
                for (j, s) in newArgs.values_immut().enumerate() {
                    ADDONEEDGE(&mut g, startArgsV + j, slotsToV[s], m);
                }
            }
        }
    }

    // color sorted by eclass id then follow by args and vars
    let mut appIdToVVec = appIdToV
        .iter()
        .map(|(x, v)| (x.id(), v))
        .collect::<Vec<_>>();
    // sort by id
    appIdToVVec.sort();
    let mut lab: Vec<i32> = vec![];
    let mut ptn = vec![];

    // color for ids
    let mut groupLen = 0;
    let mut thisGroupId = appIdToVVec[0].0;
    for (id, v) in &appIdToVVec {
        lab.push(**v as i32);
        if *id == thisGroupId {
            groupLen += 1;
        } else {
            for _ in 0..groupLen - 1 {
                ptn.push(1);
            }
            ptn.push(0);

            groupLen = 1;
            thisGroupId = *id;
        }
    }
    assert!(groupLen > 0);
    for _ in 0..groupLen - 1 {
        ptn.push(1);
    }
    ptn.push(0);
    // println!("currLabLen after ids color {}", lab.len());

    // color for args
    if argsV.len() > 0 {
        lab.extend(argsV.iter().map(|i| *i as i32));
        for _ in 0..argsV.len() - 1 {
            ptn.push(1);
        }
        ptn.push(0);
    }

    // color for vars
    let currLabLen = lab.len();
    for i in currLabLen..totalV {
        lab.push(i as i32);
    }

    assert_eq!(totalV - currLabLen, slotsToV.len());
    if slotsToV.len() > 0 {
        for _ in 0..slotsToV.len() - 1 {
            ptn.push(1);
        }
        ptn.push(0);
    }

    // output structures
    let mut orbits = vec![0; totalV];
    let mut canonG = empty_graph(m, totalV);
    let mut stats = statsblk::default();

    let mut options = optionblk::default();
    options.getcanon = TRUE; // Compute canonical labeling
    options.defaultptn = FALSE; // Use custom lab and ptn for colors

    assert_eq!(lab.len(), totalV);
    assert_eq!(ptn.len(), totalV);
    assert!(g.len() == (m * totalV));
    assert!(canonG.len() == (m * totalV));
    assert!(*lab.iter().max().unwrap() == (totalV - 1) as i32);

    unsafe {
        densenauty(
            g.as_mut_ptr(),
            lab.as_mut_ptr(),
            // if ptn[i] = 0, then a group (colour class) ends at position i
            ptn.as_mut_ptr(),
            orbits.as_mut_ptr(),
            &mut options,
            &mut stats,
            m as c_int,
            totalV as c_int,
            canonG.as_mut_ptr(),
        );
    }

    // the value of lab on return is the canonical labelling
    // of the graph. Precisely, it lists the vertices of g in the order in which they need to
    // be relabelled to give canong

    let ret = (
        lab,
        appIdToV
            .into_iter()
            .map(|(x, v)| ((*x).clone(), v))
            .collect(),
        slotsToV,
    );

    cache
        .getCacheMut()
        .insert((appIdsVec.clone(), allPerms.clone()), ret.clone());

    ret
}

pub fn canonAppIdsWithRename(
    appIdsVec: &Vec<&AppliedId>,
    allPerms: Option<&Vec<Vec<ProvenPerm>>>,
    cache: &CanonAppIdsCache,
) -> (Vec<i32>, Vec<(AppliedId, usize)>, BTreeMap<Slot, usize>) {
    if appIdsVec.len() == 0 {
        return (vec![], vec![], BTreeMap::new());
    }

    // TODO: vals in input appIds must start from 0, 1,...

    let (appIdsVec, allPerms, idMap, slotMaps) = renameAppIdsAndPerms(appIdsVec, allPerms);

    let (lab, appIdToV, slotsToV) = canonAppIdsInternal(&appIdsVec, &allPerms, cache);
    let appIdToV = translateBack(&appIdToV, &idMap, &slotMaps);

    (lab, appIdToV, slotsToV)
}

pub fn checkDedup(
    eclassId: Id,
    vec: &OrderVec<AppliedIdOrStar>,
    cache: &CanonAppIdsCache,
) -> Result<(), String> {
    let mut dedup = vec.sorted(cache);
    dedup.dedup();
    if dedup.len() != vec.len() {
        return Err(format!("dedup failed at {eclassId}"));
    }
    Ok(())
}

// This only works with Vector of AppIds
pub fn sortAppId(
    appIdsOrigs: &Vec<AppliedId>,
    dedup: bool,
    cache: &CanonAppIdsCache,
) -> Vec<AppliedId> {
    if appIdsOrigs.len() == 0 {
        return vec![];
    }

    let mut appIdsSorted = appIdsOrigs.clone();
    appIdsSorted.sort();
    if dedup {
        appIdsSorted.dedup();
    }

    let appIdsSet = appIdsSorted.iter().map(|x| x.id()).collect::<BTreeSet<_>>();
    if appIdsSet.len() == appIdsSorted.len() {
        return appIdsSorted;
    }
    debug!("start sortAppId");
    let (lab, appIdToV, _) = canonAppIdsWithRename(&appIdsSorted.iter().collect(), None, cache);

    let mut VToAppIds = BTreeMap::new();
    for (id, v) in appIdToV {
        assert!(VToAppIds.insert(v, id).is_none());
    }

    let mut sortedAppIds = vec![];
    for i in &lab[0..appIdsSorted.len()] {
        sortedAppIds.push(VToAppIds[&(*i as usize)].clone());
    }
    sortedAppIds.dedup();

    debug!("done sortAppId");
    sortedAppIds
}

pub fn weakShapeAppIds<L: LanguageChildren>(appIds: &Vec<L>) -> (Vec<L>, SlotMap) {
    let m = &mut (SlotMap::new(), 0);
    let mut appIds = appIds.clone();

    for a in appIds.iter_mut() {
        a.weak_shape_impl(m);
    }

    (appIds, m.0.inverse())
}
