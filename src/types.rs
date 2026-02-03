use crate::*;
use log::{error, info};
use nauty_Traces_sys::{
    densenauty, empty_graph, optionblk, statsblk, ADDONEEDGE, FALSE, SETWORDSNEEDED, TRUE,
};
use std::collections::{BTreeMap, BTreeSet};
use std::os::raw::c_int;

/// Ids identify e-classes.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Id(pub usize);

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

    pub fn apply_slotmap_intersect(&self, m: &SlotMap) -> AppliedId {
        AppliedId::new(self.id, self.m.compose_intersect(m))
    }

    pub fn applySlotMapPartial(&self, m: &SlotMap) -> AppliedId {
        AppliedId::new(self.id, self.m.composePartial(m))
    }

    pub fn apply_slotmap_fresh(&self, m: &SlotMap) -> AppliedId {
        AppliedId::new(self.id, self.m.compose_fresh(m))
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

// This only works with Vector of AppIds
pub fn sortAppId<L: LanguageChildren>(appIdsOrigs: &Vec<L>) -> Vec<L> {
    if appIdsOrigs.len() == 0 {
        return vec![];
    }

    let mut appIdsSorted = appIdsOrigs.clone();
    appIdsSorted.sort();
    appIdsSorted.dedup();

    let appIdsSet = appIdsSorted.iter().map(|x| x.id()).collect::<BTreeSet<_>>();
    if appIdsSet.len() == appIdsSorted.len() {
        return appIdsSorted;
    }
    info!("start sortAppId");

    // {f(x, y), f(y, x), g(x, y)}
    // should have a color order f < g < arg < var
    // 1(f) - 2(arg) - 3(arg)
    // 1(f) - 4(arg) - 5(arg)
    // 6(g) - 7(arg) - 8(arg)
    // 2(arg) - 9(var)
    // 4(arg) - 10(var)
    // 3(arg) - 10(var)
    // 5(arg) - 9(var)
    // 7(arg) - 9(var)
    // 8(arg) - 10(var)

    let mut totalV = 0;
    // total number of vertices = sum (1 + nums_function_args) + nums_variables
    let mut allSlots: BTreeSet<Slot> = BTreeSet::new();
    // must be vec because there might be duplicates
    let mut appIdToV = Vec::new();
    let mut argsV = vec![];
    for child in appIdsSorted.iter() {
        appIdToV.push((child, totalV));
        for i in 0..child.len() {
            argsV.push(totalV + i + 1);
        }
        totalV += 1 + child.len();
        allSlots.extend(child.public_slot_occurrences_iter());
    }

    let mut slotsToV = BTreeMap::new();
    for s in allSlots {
        slotsToV.insert(s, totalV);
        // println!("slotsToV {s} {totalV}");
        totalV += 1;
    }

    let m = SETWORDSNEEDED(totalV);
    let mut g = empty_graph(m, totalV);

    // add edges
    let mut curr = 0;
    for (_i, child) in appIdsSorted.iter().enumerate() {
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

            // 2(arg) - 9(var)
            ADDONEEDGE(&mut g, curr, slotsToV[&s], m);
            curr += 1;
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
    // println!("totalV {totalV}");
    // println!("currLabLen {currLabLen}");
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
            ptn.as_mut_ptr(),
            orbits.as_mut_ptr(),
            &mut options,
            &mut stats,
            m as c_int,
            totalV as c_int,
            canonG.as_mut_ptr(),
        );
    }

    let mut VToAppIds = BTreeMap::new();
    for (id, v) in appIdToV {
        assert!(VToAppIds.insert(v, id).is_none());
    }

    let mut sortedAppIds = vec![];
    for i in &lab[0..appIdsSorted.len()] {
        sortedAppIds.push(VToAppIds[&(*i as usize)].clone());
    }
    sortedAppIds.dedup();

    info!("done sortAppId");
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
