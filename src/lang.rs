use core::panic;

use crate::*;
use either::Either;

use log::debug;

#[derive(Debug, Clone)]
pub enum SyntaxElem {
    String(String), // used for identitifers and payloads
    AppliedId(AppliedId),
    Slot(Slot),
    Vec(Vec<SyntaxElem>),
    Star(u32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LanguageChildrenType {
    Slot(Slot),
    AppliedId(AppliedId),
    Star,
    Vec(Vec<LanguageChildrenType>),
    Bind,
    Bare,
}

pub fn checkChildrenTypeEq(a: &Vec<LanguageChildrenType>, b: &Vec<LanguageChildrenType>) -> bool {
    if a.len() == 0 || b.len() == 0 {
        if a.len() != 0 || b.len() != 0 {
            debug!("a = {a:#?}");
            debug!("b = {b:#?}");
            debug!("return false 0");
            return false;
        }
    }

    for i in 0..a.len().min(b.len()) {
        match (&a[i], &b[i]) {
            (LanguageChildrenType::Vec(a_), LanguageChildrenType::Vec(b_)) => {
                if !checkChildrenTypeEq(&a_, &b_) {
                    debug!("a = {a:#?}");
                    debug!("b = {b:#?}");
                    debug!("return false 1");
                    return false;
                }
            }
            (LanguageChildrenType::Star, _) | (_, LanguageChildrenType::Star) => {
                assert!(i == a.len() - 1 || i == b.len() - 1);
                debug!("a = {a:#?}");
                debug!("b = {b:#?}");
                debug!("return true 1");
                return true;
            }
            _ => {
                if a[i] != b[i] {
                    debug!("a = {a:#?}");
                    debug!("b = {b:#?}");
                    debug!("return false 2");
                    return false;
                }
            }
        }
    }

    debug!("a = {a:#?}");
    debug!("b = {b:#?}");
    debug!("return true 2");
    true
}

pub trait LanguageChildren: Debug + Clone + Hash + Eq {
    // TODO: add private_slot_occurrences aswell!
    fn all_slot_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut Slot>;
    fn public_slot_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut Slot>;
    fn applied_id_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut AppliedId>;

    fn all_slot_occurrences_iter(&self) -> impl Iterator<Item = &Slot>;
    fn public_slot_occurrences_iter(&self) -> impl Iterator<Item = &Slot>;
    fn applied_id_occurrences_iter(&self) -> impl Iterator<Item = &AppliedId>;

    fn to_syntax(&self) -> Vec<SyntaxElem>;
    fn from_syntax(_: &[SyntaxElem]) -> Option<Self>;
    fn get_type(&self) -> LanguageChildrenType;
    fn expandChildren(&mut self, id: AppliedId);

    fn weak_shape_impl(&mut self, _m: &mut (SlotMap, u32)) {
        todo!()
    }
}

fn on_see_slot(s: &mut Slot, m: &mut (SlotMap, u32)) {
    if let Some(s2) = m.0.get(*s) {
        *s = s2;
    } else {
        add_slot(s, m);
    }
}

fn add_slot(s: &mut Slot, m: &mut (SlotMap, u32)) {
    let s2 = Slot::numeric(m.1);
    m.1 += 1;
    m.0.insert(*s, s2);
    *s = s2;
}

impl LanguageChildren for AppliedId {
    fn all_slot_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut Slot> {
        self.m.values_mut()
    }
    fn public_slot_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut Slot> {
        self.m.values_mut()
    }
    fn applied_id_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut AppliedId> {
        std::iter::once(self)
    }

    fn all_slot_occurrences_iter(&self) -> impl Iterator<Item = &Slot> {
        self.m.values_immut()
    }
    fn public_slot_occurrences_iter(&self) -> impl Iterator<Item = &Slot> {
        self.m.values_immut()
    }
    fn applied_id_occurrences_iter(&self) -> impl Iterator<Item = &AppliedId> {
        std::iter::once(self)
    }

    fn to_syntax(&self) -> Vec<SyntaxElem> {
        vec![SyntaxElem::AppliedId(self.clone())]
    }
    fn from_syntax(elems: &[SyntaxElem]) -> Option<Self> {
        match elems {
            [SyntaxElem::AppliedId(x)] => Some(x.clone()),
            [] => None,
            _ => {
                panic!(
                    "(Pond) slotted_egraphs::lang::AppliedId::from_syntax: expected a single applied id, got {:?}",
                    elems
                );
            }
        }
    }
    fn get_type(&self) -> LanguageChildrenType {
        LanguageChildrenType::AppliedId(self.clone())
    }

    fn expandChildren(&mut self, id: AppliedId) {}

    fn weak_shape_impl(&mut self, m: &mut (SlotMap, u32)) {
        for x in self.m.values_mut() {
            on_see_slot(x, m);
        }
    }
}

impl LanguageChildren for Slot {
    fn all_slot_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut Slot> {
        std::iter::once(self)
    }
    fn public_slot_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut Slot> {
        std::iter::once(self)
    }
    fn applied_id_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut AppliedId> {
        std::iter::empty()
    }

    fn all_slot_occurrences_iter(&self) -> impl Iterator<Item = &Slot> {
        std::iter::once(self)
    }
    fn public_slot_occurrences_iter(&self) -> impl Iterator<Item = &Slot> {
        std::iter::once(self)
    }
    fn applied_id_occurrences_iter(&self) -> impl Iterator<Item = &AppliedId> {
        std::iter::empty()
    }

    fn to_syntax(&self) -> Vec<SyntaxElem> {
        vec![SyntaxElem::Slot(*self)]
    }
    fn from_syntax(elems: &[SyntaxElem]) -> Option<Self> {
        match elems {
            [SyntaxElem::Slot(x)] => Some(x.clone()),
            [] => None,
            _ => {
                panic!(
                    "(Pond) slotted_egraphs::slot::Slot::from_syntax: expected a single slot, got {:?}",
                    elems
                );
            }
        }
    }
    fn get_type(&self) -> LanguageChildrenType {
        LanguageChildrenType::Slot(self.clone())
    }

    fn expandChildren(&mut self, id: AppliedId) {}

    fn weak_shape_impl(&mut self, m: &mut (SlotMap, u32)) {
        on_see_slot(self, m);
    }
}

/// Implements [LanguageChildren] for payload types that are independent of Slots. For example u32, String etc.
#[macro_export]
macro_rules! bare_language_child {
    ($($id:ident),*) => {
        $(
        impl LanguageChildren for $id {
            fn all_slot_occurrences_iter_mut(&mut self) -> impl Iterator<Item=&mut Slot> { std::iter::empty() }
            fn public_slot_occurrences_iter_mut(&mut self) -> impl Iterator<Item=&mut Slot> { std::iter::empty() }
            fn applied_id_occurrences_iter_mut(&mut self) -> impl Iterator<Item=&mut AppliedId> { std::iter::empty() }

            fn all_slot_occurrences_iter(&self) -> impl Iterator<Item=&Slot> { std::iter::empty() }
            fn public_slot_occurrences_iter(&self) -> impl Iterator<Item=&Slot> { std::iter::empty() }
            fn applied_id_occurrences_iter(&self) -> impl Iterator<Item=&AppliedId> { std::iter::empty() }

            fn to_syntax(&self) -> Vec<SyntaxElem> { vec![SyntaxElem::String(self.to_string())] }
            fn from_syntax(elems: &[SyntaxElem]) -> Option<Self> {
                debug!("L(Bare)::from_syntax with elems = {:?}", elems);
                match elems {
                    [SyntaxElem::String(x)] => x.parse().ok(),
                    _ => {
                        panic!(
                            "(Pond) slotted_egraphs::lang::Bind::from_syntax: expected a single string, got {:?}",
                            elems
                        );
                    },
                }
            }
            fn get_type(&self) -> LanguageChildrenType {
                LanguageChildrenType::Bare
            }

            fn expandChildren(&mut self, id: AppliedId) {}

            fn weak_shape_impl(&mut self, _m: &mut (SlotMap, u32)) {}
        }
        )*
    }
}

bare_language_child!(
    u128, u64, u32, u16, u8, i128, i64, i32, i16, i8, usize, isize, bool, char, Symbol, String
);

#[derive(Hash, PartialEq, Eq, Debug, Clone, PartialOrd, Ord)]
pub struct Bind<T> {
    pub slot: Slot,
    pub elem: T,
}

impl LanguageChildren for AppliedIdOrStar {
    fn all_slot_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut Slot> {
        match self {
            AppliedIdOrStar::AppliedId(x) => x.all_slot_occurrences_iter_mut(),
            AppliedIdOrStar::Star(_) => todo!(),
        }
    }

    fn public_slot_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut Slot> {
        match self {
            AppliedIdOrStar::AppliedId(x) => x.public_slot_occurrences_iter_mut(),
            AppliedIdOrStar::Star(_) => todo!(),
        }
    }

    fn applied_id_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut AppliedId> {
        match self {
            AppliedIdOrStar::AppliedId(x) => x.applied_id_occurrences_iter_mut(),
            AppliedIdOrStar::Star(_) => todo!(),
        }
    }

    // immut:
    fn all_slot_occurrences_iter(&self) -> impl Iterator<Item = &Slot> {
        match self {
            AppliedIdOrStar::AppliedId(x) => Either::Left(x.all_slot_occurrences_iter()),
            AppliedIdOrStar::Star(_) => Either::Right(std::iter::empty()),
        }
    }

    fn public_slot_occurrences_iter(&self) -> impl Iterator<Item = &Slot> {
        match self {
            AppliedIdOrStar::AppliedId(x) => x.public_slot_occurrences_iter(),
            AppliedIdOrStar::Star(_) => todo!(),
        }
    }

    fn applied_id_occurrences_iter(&self) -> impl Iterator<Item = &AppliedId> {
        match self {
            AppliedIdOrStar::AppliedId(x) => x.applied_id_occurrences_iter(),
            AppliedIdOrStar::Star(_) => todo!(),
        }
    }

    // syntax:
    fn to_syntax(&self) -> Vec<SyntaxElem> {
        match self {
            AppliedIdOrStar::AppliedId(x) => x.to_syntax(),
            AppliedIdOrStar::Star(n) => vec![SyntaxElem::Star(*n)],
        }
    }

    fn from_syntax(elems: &[SyntaxElem]) -> Option<Self> {
        debug!("AppliedIdOrStar::from_syntax, elems: {:?}", elems);
        match elems {
            [SyntaxElem::AppliedId(x)] => Some(AppliedIdOrStar::AppliedId(x.clone())),
            [SyntaxElem::Star(n)] => Some(AppliedIdOrStar::Star(*n)),
            [] => None,
            _ => {
                panic!("(Pond) slotted_egraphs::lang::AppliedIdOrStar::from_syntax");
            }
        }
    }

    fn get_type(&self) -> LanguageChildrenType {
        match self {
            AppliedIdOrStar::AppliedId(x) => x.get_type(),
            AppliedIdOrStar::Star(_) => LanguageChildrenType::Star,
        }
    }

    fn expandChildren(&mut self, id: AppliedId) {}

    fn weak_shape_impl(&mut self, m: &mut (SlotMap, u32)) {
        match self {
            AppliedIdOrStar::AppliedId(x) => x.weak_shape_impl(m),
            AppliedIdOrStar::Star(_) => {}
        }
    }
}

impl<L: LanguageChildren> LanguageChildren for Bind<L> {
    // mut:
    fn all_slot_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut Slot> {
        std::iter::once(&mut self.slot).chain(self.elem.all_slot_occurrences_iter_mut())
    }

    fn public_slot_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut Slot> {
        self.elem
            .public_slot_occurrences_iter_mut()
            .filter(|x| **x != self.slot)
    }

    fn applied_id_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut AppliedId> {
        self.elem.applied_id_occurrences_iter_mut()
    }

    // immut:
    fn all_slot_occurrences_iter(&self) -> impl Iterator<Item = &Slot> {
        std::iter::once(&self.slot).chain(self.elem.all_slot_occurrences_iter())
    }

    fn public_slot_occurrences_iter(&self) -> impl Iterator<Item = &Slot> {
        self.elem
            .public_slot_occurrences_iter()
            .filter(|x| **x != self.slot)
    }

    fn applied_id_occurrences_iter(&self) -> impl Iterator<Item = &AppliedId> {
        self.elem.applied_id_occurrences_iter()
    }

    // syntax:
    fn to_syntax(&self) -> Vec<SyntaxElem> {
        let mut v = vec![SyntaxElem::Slot(self.slot)];
        v.extend(self.elem.to_syntax());

        v
    }

    fn from_syntax(elems: &[SyntaxElem]) -> Option<Self> {
        let SyntaxElem::Slot(slot) = elems.get(0)? else {
            panic!(
                "(Pond) slotted_egraphs::lang::Bind::from_syntax: expected a single slot, got {:?}",
                elems
            );
        };
        let elem = L::from_syntax(&elems[1..])?;

        Some(Bind { slot: *slot, elem })
    }

    fn get_type(&self) -> LanguageChildrenType {
        LanguageChildrenType::Bind
    }

    fn expandChildren(&mut self, id: AppliedId) {}

    fn weak_shape_impl(&mut self, m: &mut (SlotMap, u32)) {
        let s = self.slot;
        add_slot(&mut self.slot, m);
        self.elem.weak_shape_impl(m);
        m.0.remove(s);
    }
}

impl<L: LanguageChildren> LanguageChildren for Vec<L> {
    fn all_slot_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut Slot> {
        self.into_iter()
            .flat_map(|x| x.all_slot_occurrences_iter_mut())
    }

    fn public_slot_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut Slot> {
        self.into_iter()
            .flat_map(|x| x.public_slot_occurrences_iter_mut())
    }

    fn applied_id_occurrences_iter_mut(&mut self) -> impl Iterator<Item = &mut AppliedId> {
        self.into_iter()
            .flat_map(|x| x.applied_id_occurrences_iter_mut())
    }

    // immut:
    fn all_slot_occurrences_iter(&self) -> impl Iterator<Item = &Slot> {
        self.iter().flat_map(|x| x.all_slot_occurrences_iter())
    }

    fn public_slot_occurrences_iter(&self) -> impl Iterator<Item = &Slot> {
        self.iter().flat_map(|x| x.public_slot_occurrences_iter())
    }

    fn applied_id_occurrences_iter(&self) -> impl Iterator<Item = &AppliedId> {
        self.iter().flat_map(|x| x.applied_id_occurrences_iter())
    }

    // syntax:
    fn to_syntax(&self) -> Vec<SyntaxElem> {
        self.iter().flat_map(|x| x.to_syntax()).collect()
    }

    fn from_syntax(elems: &[SyntaxElem]) -> Option<Self> {
        debug!("vec<L>::from_syntax input elems = {:?}", elems);
        let mut out = Vec::new();
        if elems.is_empty() {
            debug!("vec<L>::from_syntax return None1");
            return None;
        }

        match elems {
            [SyntaxElem::Vec(v)] => {
                for x in v {
                    let arr = [x.clone()];
                    if let Some(y) = L::from_syntax(&arr) {
                        out.push(y);
                    } else {
                        debug!("vec<L>::from_syntax return None2");
                        return None;
                    }
                }

                Some(out)
            }
            _ => panic!(""),
        }

        // (Pond): If you want to use * for vec, please use it like this: <*>

        // Some(out)
    }

    fn get_type(&self) -> LanguageChildrenType {
        let mut out = Vec::new();
        for x in self {
            out.push(x.get_type());
        }
        LanguageChildrenType::Vec(out)
    }

    fn expandChildren(&mut self, id: AppliedId) {}

    fn weak_shape_impl(&mut self, m: &mut (SlotMap, u32)) {
        for x in self {
            x.weak_shape_impl(m);
        }
    }
}

// TODO: add LanguageChildren definition for tuples.

/// A trait to define your Language (i.e. your E-Node type).
pub trait Language: Debug + Clone + Hash + Eq + Ord {
    /// List the mutable references of all child [Slot]s in your E-Node, in order of occurrence.
    fn all_slot_occurrences_mut(&mut self) -> Vec<&mut Slot>;

    /// List the mutable references to all *public* child [Slot]s in your E-Node, in order of occurrence.
    ///
    /// Public Slots are those, which are visible from the outside of that e-node.
    /// * A typical example would be a `(var $x)` e-node, which has a *public* slot `$x`.
    /// * A typical counter-example would be the `(lam $x body)` e-node, which has a *private* slot `$x`.
    fn public_slot_occurrences_mut(&mut self) -> Vec<&mut Slot>;

    /// List the mutable references to all child [AppliedId]s in your E-Node, in the order of occurrence.
    fn applied_id_occurrences_mut(&mut self) -> Vec<&mut AppliedId>;

    fn all_slot_occurrences(&self) -> Vec<Slot>;
    fn public_slot_occurrences(&self) -> Vec<Slot>;
    fn applied_id_occurrences(&self) -> Vec<&AppliedId>;

    /// This function will be used to display your E-Node.
    fn to_syntax(&self) -> Vec<SyntaxElem>;

    /// This function will be used to parse your E-Node.
    fn from_syntax(_: &[SyntaxElem]) -> Option<Self>;

    fn slots(&self) -> SmallHashSet<Slot>;
    fn weak_shape_inplace(&mut self) -> Bijection;

    fn getChildrenType(&self) -> Vec<LanguageChildrenType>;
    fn expandChildren(&mut self, id: AppliedId);

    #[track_caller]
    #[doc(hidden)]
    fn check(&self) {
        let mut c = self.clone();
        let all: HashSet<*mut Slot> = c
            .all_slot_occurrences_mut()
            .into_iter()
            .map(|x| x as *mut Slot)
            .collect();
        let public: HashSet<*mut Slot> = c
            .public_slot_occurrences_mut()
            .into_iter()
            .map(|x| x as *mut Slot)
            .collect();
        let private: HashSet<*mut Slot> = c
            .private_slot_occurrences_mut()
            .into_iter()
            .map(|x| x as *mut Slot)
            .collect();

        assert!(public.is_disjoint(&private));

        // This also catches errors, where different Slot-addresses have the same slot names. This also counts as a collision!
        let f = |x: Vec<Slot>| x.into_iter().collect::<HashSet<_>>();
        assert!(f(c.public_slot_occurrences()).is_disjoint(&f(c.private_slot_occurrences())));

        let all2: HashSet<*mut Slot> = public.union(&private).copied().collect();
        assert_eq!(all2, all);
    }

    // generated methods:

    #[doc(hidden)]
    fn private_slot_occurrences_mut(&mut self) -> Vec<&mut Slot> {
        let public = self.public_slot_occurrences();
        let mut out = self.all_slot_occurrences_mut();
        out.retain(|x| !public.contains(x));
        out
    }

    #[doc(hidden)]
    fn private_slot_occurrences(&self) -> Vec<Slot> {
        let public = self.public_slot_occurrences();
        let mut out = self.all_slot_occurrences();
        out.retain(|x| !public.contains(x));
        out
    }

    #[doc(hidden)]
    fn private_slots(&self) -> SmallHashSet<Slot> {
        self.private_slot_occurrences().into_iter().collect()
    }

    #[doc(hidden)]
    fn map_applied_ids(&self, mut f: impl FnMut(AppliedId) -> AppliedId) -> Self {
        let mut c = self.clone();
        for x in c.applied_id_occurrences_mut() {
            *x = f(x.clone());
        }
        c
    }

    // TODO m.values() might collide with your private slot names.
    // Should we rename our private slots to be safe?
    #[doc(hidden)]
    // (Pond) change(compose) the mapping of the current Enode
    // (Pond) a -> b, change with b -> c, to a -> c.
    fn apply_slotmap_partial(&self, m: &SlotMap) -> Self {
        let mut prv = vec![].into();
        if CHECKS {
            prv = self.private_slots();
        }

        let mut c = self.clone();
        for x in c.public_slot_occurrences_mut() {
            let y = m[*x];

            // If y collides with a private slot, we have a problem.
            if CHECKS {
                assert!(!prv.contains(&y));
            }

            *x = y;
        }
        c
    }

    #[track_caller]
    #[doc(hidden)]
    fn apply_slotmap(&self, m: &SlotMap) -> Self {
        if CHECKS {
            assert!(
                m.keys().is_superset(&self.slots()),
                "Language::apply_slotmap: The SlotMap doesn't map all free slots!"
            );
        }
        self.apply_slotmap_partial(m)
    }

    #[doc(hidden)]
    fn apply_slotmap_fresh(&self, m: &SlotMap) -> Self {
        let mut prv = vec![].into();
        if CHECKS {
            prv = self.private_slots();
        }

        let mut c = self.clone();
        for x in c.public_slot_occurrences_mut() {
            let y = m.get(*x).unwrap_or_else(Slot::fresh);

            // If y collides with a private slot, we have a problem.
            if CHECKS {
                assert!(!prv.contains(&y));
            }

            *x = y;
        }
        c
    }

    // (Pond) get children ids
    #[doc(hidden)]
    fn ids(&self) -> Vec<Id> {
        self.applied_id_occurrences()
            .into_iter()
            .map(|x| x.id)
            .collect()
    }

    // let n.weak_shape() = (sh, bij); then
    // - sh.apply_slotmap(bij) is equivalent to n (excluding lambda variable renames)
    // - bij.slots() == n.slots(). Note that these would also include redundant slots.
    // - sh is the lexicographically lowest equivalent version of n, reachable by bijective renaming of slots (including redundant ones).
    #[doc(hidden)]
    fn weak_shape(&self) -> (Self, Bijection) {
        let mut c = self.clone();
        let bij = c.weak_shape_inplace();
        (c, bij)
    }

    #[doc(hidden)]
    fn refresh_private(&self) -> Self {
        let mut c = self.clone();
        let prv: SmallHashSet<Slot> = c.private_slot_occurrences().into_iter().collect();
        let fresh = SlotMap::bijection_from_fresh_to(&prv).inverse();
        for x in c.private_slot_occurrences_mut() {
            *x = fresh[*x];
        }
        c
    }

    #[doc(hidden)]
    fn refresh_slots(&self, set: SmallHashSet<Slot>) -> Self {
        let mut c = self.clone();
        let fresh = SlotMap::bijection_from_fresh_to(&set).inverse();
        for x in c.all_slot_occurrences_mut() {
            if set.contains(x) {
                *x = fresh[*x];
            }
        }
        c
    }

    // refreshes private and redundant slots.
    // The public slots are given by `public`.
    #[doc(hidden)]
    fn refresh_internals(&self, public: SmallHashSet<Slot>) -> Self {
        let mut c = self.clone();
        let internals = &c
            .all_slot_occurrences()
            .into_iter()
            .collect::<SmallHashSet<_>>()
            - &public;
        let fresh = SlotMap::bijection_from_fresh_to(&internals).inverse();
        for x in c.all_slot_occurrences_mut() {
            if internals.contains(x) {
                *x = fresh[*x];
            }
        }
        c
    }

    fn eq_with_star() {}
}
