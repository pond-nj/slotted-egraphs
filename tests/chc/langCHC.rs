// use crate::*;

// #[derive(PartialEq, Eq, Hash, Clone, Debug, PartialOrd, Ord)]
// pub enum CHC {
//     // to specify types
//     Int(Slot),
//     Node(Slot),

//     PredSyntax(Vec<AppliedId>),
//     New(AppliedId, AppliedId, Vec<AppliedIdOrStar>),
//     Compose(Vec<AppliedIdOrStar>),
//     True(),
//     False(),

//     // node(x, l, r) has subtree l and r and element x at this node
//     BiNode(AppliedId, AppliedId, AppliedId),
//     Leaf(),

//     // Boolean
//     And(Vec<AppliedIdOrStar>),

//     // Arithmetic
//     Geq(AppliedId, AppliedId),
//     Leq(AppliedId, AppliedId),
//     Less(AppliedId, AppliedId),
//     Greater(AppliedId, AppliedId),
//     Eq(AppliedId, AppliedId),
//     Add(AppliedId, AppliedId),
//     Minus(AppliedId, AppliedId),

//     Number(u32),

//     // (composeInit predName syntax functional outputIdx)
//     // use to create empty compose eclass for recursive definition
//     ComposeInit(AppliedId, AppliedId, AppliedId, Vec<AppliedId>),
//     PredName(String),
//     // extraction control, means that we cannot extract this node
// }

// impl Language for CHC {
//     fn all_slot_occurrences_mut(&mut self) -> Vec<&mut Slot> {
//         match self {
//             CHC::Int(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Node(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::PredSyntax(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::New(a0, a1, a2) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.all_slot_occurrences_iter_mut());
//                 let out = out.chain(a2.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Compose(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::True() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::False() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::BiNode(a0, a1, a2) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.all_slot_occurrences_iter_mut());
//                 let out = out.chain(a2.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Leaf() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::And(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Geq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Leq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Less(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Greater(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Eq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Add(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Minus(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Number(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::ComposeInit(a0, a1, a2, a3) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.all_slot_occurrences_iter_mut());
//                 let out = out.chain(a2.all_slot_occurrences_iter_mut());
//                 let out = out.chain(a3.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::PredName(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//         }
//     }
//     fn public_slot_occurrences_mut(&mut self) -> Vec<&mut Slot> {
//         match self {
//             CHC::Int(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Node(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::PredSyntax(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::New(a0, a1, a2) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.public_slot_occurrences_iter_mut());
//                 let out = out.chain(a2.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Compose(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::True() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::False() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::BiNode(a0, a1, a2) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.public_slot_occurrences_iter_mut());
//                 let out = out.chain(a2.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Leaf() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::And(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Geq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Leq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Less(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Greater(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Eq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Add(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Minus(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Number(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::ComposeInit(a0, a1, a2, a3) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 let out = out.chain(a1.public_slot_occurrences_iter_mut());
//                 let out = out.chain(a2.public_slot_occurrences_iter_mut());
//                 let out = out.chain(a3.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::PredName(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter_mut());
//                 out.collect()
//             }
//         }
//     }
//     fn applied_id_occurrences_mut(&mut self) -> Vec<&mut AppliedId> {
//         match self {
//             CHC::Int(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Node(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::PredSyntax(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::New(a0, a1, a2) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 let out = out.chain(a1.applied_id_occurrences_iter_mut());
//                 let out = out.chain(a2.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Compose(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::True() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::False() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::BiNode(a0, a1, a2) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 let out = out.chain(a1.applied_id_occurrences_iter_mut());
//                 let out = out.chain(a2.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Leaf() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::And(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Geq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 let out = out.chain(a1.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Leq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 let out = out.chain(a1.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Less(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 let out = out.chain(a1.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Greater(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 let out = out.chain(a1.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Eq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 let out = out.chain(a1.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Add(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 let out = out.chain(a1.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Minus(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 let out = out.chain(a1.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::Number(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::ComposeInit(a0, a1, a2, a3) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 let out = out.chain(a1.applied_id_occurrences_iter_mut());
//                 let out = out.chain(a2.applied_id_occurrences_iter_mut());
//                 let out = out.chain(a3.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//             CHC::PredName(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter_mut());
//                 out.collect()
//             }
//         }
//     }
//     fn all_slot_occurrences(&self) -> Vec<Slot> {
//         match self {
//             CHC::Int(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Node(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::PredSyntax(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::New(a0, a1, a2) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.all_slot_occurrences_iter().copied());
//                 let out = out.chain(a2.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Compose(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::True() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::False() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::BiNode(a0, a1, a2) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.all_slot_occurrences_iter().copied());
//                 let out = out.chain(a2.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Leaf() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::And(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Geq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Leq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Less(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Greater(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Eq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Add(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Minus(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Number(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::ComposeInit(a0, a1, a2, a3) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.all_slot_occurrences_iter().copied());
//                 let out = out.chain(a2.all_slot_occurrences_iter().copied());
//                 let out = out.chain(a3.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::PredName(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.all_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//         }
//     }
//     fn public_slot_occurrences(&self) -> Vec<Slot> {
//         match self {
//             CHC::Int(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Node(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::PredSyntax(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::New(a0, a1, a2) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a2.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Compose(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::True() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::False() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::BiNode(a0, a1, a2) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a2.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Leaf() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::And(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Geq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Leq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Less(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Greater(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Eq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Add(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Minus(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Number(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::ComposeInit(a0, a1, a2, a3) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a2.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a3.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::PredName(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//         }
//     }
//     fn applied_id_occurrences(&self) -> Vec<&AppliedId> {
//         match self {
//             CHC::Int(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::Node(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::PredSyntax(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::New(a0, a1, a2) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 let out = out.chain(a1.applied_id_occurrences_iter());
//                 let out = out.chain(a2.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::Compose(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::True() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::False() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::BiNode(a0, a1, a2) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 let out = out.chain(a1.applied_id_occurrences_iter());
//                 let out = out.chain(a2.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::Leaf() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::And(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::Geq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 let out = out.chain(a1.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::Leq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 let out = out.chain(a1.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::Less(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 let out = out.chain(a1.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::Greater(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 let out = out.chain(a1.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::Eq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 let out = out.chain(a1.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::Add(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 let out = out.chain(a1.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::Minus(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 let out = out.chain(a1.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::Number(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::ComposeInit(a0, a1, a2, a3) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 let out = out.chain(a1.applied_id_occurrences_iter());
//                 let out = out.chain(a2.applied_id_occurrences_iter());
//                 let out = out.chain(a3.applied_id_occurrences_iter());
//                 out.collect()
//             }
//             CHC::PredName(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.applied_id_occurrences_iter());
//                 out.collect()
//             }
//         }
//     }
//     fn to_syntax(&self) -> Vec<SyntaxElem> {
//         match self {
//             CHC::Int(a0) => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("int"))];
//                 out.extend(a0.to_syntax());
//                 out
//             }
//             CHC::Node(a0) => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("node"))];
//                 out.extend(a0.to_syntax());
//                 out
//             }
//             CHC::PredSyntax(a0) => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("pred"))];
//                 out.extend(a0.to_syntax());
//                 out
//             }
//             CHC::New(a0, a1, a2) => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("new"))];
//                 out.extend(a0.to_syntax());
//                 out.extend(a1.to_syntax());
//                 out.extend(a2.to_syntax());
//                 out
//             }
//             CHC::Compose(a0) => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("compose"))];
//                 out.extend(a0.to_syntax());
//                 out
//             }
//             CHC::True() => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("true"))];
//                 out
//             }
//             CHC::False() => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("false"))];
//                 out
//             }
//             CHC::BiNode(a0, a1, a2) => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("binode"))];
//                 out.extend(a0.to_syntax());
//                 out.extend(a1.to_syntax());
//                 out.extend(a2.to_syntax());
//                 out
//             }
//             CHC::Leaf() => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("leaf"))];
//                 out
//             }
//             CHC::And(a0) => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("and"))];
//                 out.extend(a0.to_syntax());
//                 out
//             }
//             CHC::Geq(a0, a1) => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("geq"))];
//                 out.extend(a0.to_syntax());
//                 out.extend(a1.to_syntax());
//                 out
//             }
//             CHC::Leq(a0, a1) => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("leq"))];
//                 out.extend(a0.to_syntax());
//                 out.extend(a1.to_syntax());
//                 out
//             }
//             CHC::Less(a0, a1) => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("lt"))];
//                 out.extend(a0.to_syntax());
//                 out.extend(a1.to_syntax());
//                 out
//             }
//             CHC::Greater(a0, a1) => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("gt"))];
//                 out.extend(a0.to_syntax());
//                 out.extend(a1.to_syntax());
//                 out
//             }
//             CHC::Eq(a0, a1) => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("eq"))];
//                 out.extend(a0.to_syntax());
//                 out.extend(a1.to_syntax());
//                 out
//             }
//             CHC::Add(a0, a1) => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("+"))];
//                 out.extend(a0.to_syntax());
//                 out.extend(a1.to_syntax());
//                 out
//             }
//             CHC::Minus(a0, a1) => {
//                 let mut out: Vec<SyntaxElem> = vec![SyntaxElem::String(String::from("-"))];
//                 out.extend(a0.to_syntax());
//                 out.extend(a1.to_syntax());
//                 out
//             }
//             CHC::Number(a0) => a0.to_syntax(),
//             CHC::ComposeInit(a0, a1, a2, a3) => {
//                 let mut out: Vec<SyntaxElem> =
//                     vec![SyntaxElem::String(String::from("composeInit"))];
//                 out.extend(a0.to_syntax());
//                 out.extend(a1.to_syntax());
//                 out.extend(a2.to_syntax());
//                 out.extend(a3.to_syntax());
//                 out
//             }
//             CHC::PredName(a0) => a0.to_syntax(),
//         }
//     }
//     fn from_syntax(elems: &[SyntaxElem]) -> Option<Self> {
//         let SyntaxElem::String(op) = elems.get(0)? else {
//             return None;
//         };
//         let ret = match &**op {
//             "int" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <Slot>::from_syntax(a)
//                     })
//                     .next();
//                 let a0 = tmp?;
//                 children = rest;
//                 Some(CHC::Int(a0))
//             }
//             "node" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <Slot>::from_syntax(a)
//                     })
//                     .next();
//                 let a0 = tmp?;
//                 children = rest;
//                 Some(CHC::Node(a0))
//             }
//             "pred" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <Vec<AppliedId>>::from_syntax(a)
//                     })
//                     .next();
//                 let a0 = tmp?;
//                 children = rest;
//                 Some(CHC::PredSyntax(a0))
//             }
//             "new" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a0 = tmp?;
//                 children = rest;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a1 = tmp?;
//                 children = rest;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <Vec<AppliedIdOrStar>>::from_syntax(a)
//                     })
//                     .next();
//                 let a2 = tmp?;
//                 children = rest;
//                 Some(CHC::New(a0, a1, a2))
//             }
//             "compose" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <Vec<AppliedIdOrStar>>::from_syntax(a)
//                     })
//                     .next();
//                 let a0 = tmp?;
//                 children = rest;
//                 Some(CHC::Compose(a0))
//             }
//             "true" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 Some(CHC::True())
//             }
//             "false" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 Some(CHC::False())
//             }
//             "binode" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a0 = tmp?;
//                 children = rest;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a1 = tmp?;
//                 children = rest;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a2 = tmp?;
//                 children = rest;
//                 Some(CHC::BiNode(a0, a1, a2))
//             }
//             "leaf" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 Some(CHC::Leaf())
//             }
//             "and" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <Vec<AppliedIdOrStar>>::from_syntax(a)
//                     })
//                     .next();
//                 let a0 = tmp?;
//                 children = rest;
//                 Some(CHC::And(a0))
//             }
//             "geq" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a0 = tmp?;
//                 children = rest;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a1 = tmp?;
//                 children = rest;
//                 Some(CHC::Geq(a0, a1))
//             }
//             "leq" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a0 = tmp?;
//                 children = rest;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a1 = tmp?;
//                 children = rest;
//                 Some(CHC::Leq(a0, a1))
//             }
//             "lt" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a0 = tmp?;
//                 children = rest;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a1 = tmp?;
//                 children = rest;
//                 Some(CHC::Less(a0, a1))
//             }
//             "gt" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a0 = tmp?;
//                 children = rest;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a1 = tmp?;
//                 children = rest;
//                 Some(CHC::Greater(a0, a1))
//             }
//             "eq" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a0 = tmp?;
//                 children = rest;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a1 = tmp?;
//                 children = rest;
//                 Some(CHC::Eq(a0, a1))
//             }
//             "+" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a0 = tmp?;
//                 children = rest;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a1 = tmp?;
//                 children = rest;
//                 Some(CHC::Add(a0, a1))
//             }
//             "-" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a0 = tmp?;
//                 children = rest;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a1 = tmp?;
//                 children = rest;
//                 Some(CHC::Minus(a0, a1))
//             }
//             "composeInit" => {
//                 let mut children = &elems[1..];
//                 let mut rest = children;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a0 = tmp?;
//                 children = rest;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a1 = tmp?;
//                 children = rest;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <AppliedId>::from_syntax(a)
//                     })
//                     .next();
//                 let a2 = tmp?;
//                 children = rest;
//                 let mut tmp = (0..=children.len())
//                     .filter_map(|n| {
//                         let a = &children[..n];
//                         rest = &children[n..];
//                         <Vec<AppliedId>>::from_syntax(a)
//                     })
//                     .next();
//                 let a3 = tmp?;
//                 children = rest;
//                 Some(CHC::ComposeInit(a0, a1, a2, a3))
//             }
//             _ => {
//                 if let Some(a) = <u32>::from_syntax(elems) {
//                     return Some(CHC::Number(a));
//                 }
//                 if let Some(a) = <String>::from_syntax(elems) {
//                     return Some(CHC::PredName(a));
//                 }
//                 None
//             }
//         };
//         ret
//     }
//     fn slots(&self) -> slotted_egraphs::SmallHashSet<Slot> {
//         match self {
//             CHC::Int(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Node(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::PredSyntax(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::New(a0, a1, a2) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a2.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Compose(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::True() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::False() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::BiNode(a0, a1, a2) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a2.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Leaf() => {
//                 let out = std::iter::empty();
//                 out.collect()
//             }
//             CHC::And(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Geq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Leq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Less(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Greater(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Eq(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Add(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Minus(a0, a1) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::Number(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::ComposeInit(a0, a1, a2, a3) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a1.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a2.public_slot_occurrences_iter().copied());
//                 let out = out.chain(a3.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//             CHC::PredName(a0) => {
//                 let out = std::iter::empty();
//                 let out = out.chain(a0.public_slot_occurrences_iter().copied());
//                 out.collect()
//             }
//         }
//     }
//     fn weak_shape_inplace(&mut self) -> slotted_egraphs::SlotMap {
//         let m = &mut (slotted_egraphs::SlotMap::new(), 0);
//         match self {
//             CHC::Int(a0) => {
//                 a0.weak_shape_impl(m);
//             }
//             CHC::Node(a0) => {
//                 a0.weak_shape_impl(m);
//             }
//             CHC::PredSyntax(a0) => {
//                 a0.weak_shape_impl(m);
//             }
//             CHC::New(a0, a1, a2) => {
//                 a0.weak_shape_impl(m);
//                 a1.weak_shape_impl(m);
//                 a2.weak_shape_impl(m);
//             }
//             CHC::Compose(a0) => {
//                 a0.weak_shape_impl(m);
//             }
//             CHC::True() => {}
//             CHC::False() => {}
//             CHC::BiNode(a0, a1, a2) => {
//                 a0.weak_shape_impl(m);
//                 a1.weak_shape_impl(m);
//                 a2.weak_shape_impl(m);
//             }
//             CHC::Leaf() => {}
//             CHC::And(a0) => {
//                 a0.weak_shape_impl(m);
//             }
//             CHC::Geq(a0, a1) => {
//                 a0.weak_shape_impl(m);
//                 a1.weak_shape_impl(m);
//             }
//             CHC::Leq(a0, a1) => {
//                 a0.weak_shape_impl(m);
//                 a1.weak_shape_impl(m);
//             }
//             CHC::Less(a0, a1) => {
//                 a0.weak_shape_impl(m);
//                 a1.weak_shape_impl(m);
//             }
//             CHC::Greater(a0, a1) => {
//                 a0.weak_shape_impl(m);
//                 a1.weak_shape_impl(m);
//             }
//             CHC::Eq(a0, a1) => {
//                 a0.weak_shape_impl(m);
//                 a1.weak_shape_impl(m);
//             }
//             CHC::Add(a0, a1) => {
//                 a0.weak_shape_impl(m);
//                 a1.weak_shape_impl(m);
//             }
//             CHC::Minus(a0, a1) => {
//                 a0.weak_shape_impl(m);
//                 a1.weak_shape_impl(m);
//             }
//             CHC::Number(a0) => {
//                 a0.weak_shape_impl(m);
//             }
//             CHC::ComposeInit(a0, a1, a2, a3) => {
//                 a0.weak_shape_impl(m);
//                 a1.weak_shape_impl(m);
//                 a2.weak_shape_impl(m);
//                 a3.weak_shape_impl(m);
//             }
//             CHC::PredName(a0) => {
//                 a0.weak_shape_impl(m);
//             }
//         }
//         m.0.inverse()
//     }
//     fn getChildrenType(&self) -> Vec<slotted_egraphs::LanguageChildrenType> {
//         match self {
//             CHC::Int(a0) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out
//             }
//             CHC::Node(a0) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out
//             }
//             CHC::PredSyntax(a0) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out
//             }
//             CHC::New(a0, a1, a2) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out.push(a1.get_type());
//                 out.push(a2.get_type());
//                 out
//             }
//             CHC::Compose(a0) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out
//             }
//             CHC::True() => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out
//             }
//             CHC::False() => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out
//             }
//             CHC::BiNode(a0, a1, a2) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out.push(a1.get_type());
//                 out.push(a2.get_type());
//                 out
//             }
//             CHC::Leaf() => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out
//             }
//             CHC::And(a0) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out
//             }
//             CHC::Geq(a0, a1) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out.push(a1.get_type());
//                 out
//             }
//             CHC::Leq(a0, a1) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out.push(a1.get_type());
//                 out
//             }
//             CHC::Less(a0, a1) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out.push(a1.get_type());
//                 out
//             }
//             CHC::Greater(a0, a1) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out.push(a1.get_type());
//                 out
//             }
//             CHC::Eq(a0, a1) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out.push(a1.get_type());
//                 out
//             }
//             CHC::Add(a0, a1) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out.push(a1.get_type());
//                 out
//             }
//             CHC::Minus(a0, a1) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out.push(a1.get_type());
//                 out
//             }
//             CHC::Number(a0) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out
//             }
//             CHC::ComposeInit(a0, a1, a2, a3) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out.push(a1.get_type());
//                 out.push(a2.get_type());
//                 out.push(a3.get_type());
//                 out
//             }
//             CHC::PredName(a0) => {
//                 let mut out: Vec<LanguageChildrenType> = vec![];
//                 out.push(a0.get_type());
//                 out
//             }
//         }
//     }
//     fn expandChildren(&mut self) {
//         match self {
//             CHC::Int(a0) => {
//                 a0.expandChildren();
//             }
//             CHC::Node(a0) => {
//                 a0.expandChildren();
//             }
//             CHC::PredSyntax(a0) => {
//                 a0.expandChildren();
//             }
//             CHC::New(a0, a1, a2) => {
//                 a0.expandChildren();
//                 a1.expandChildren();
//                 a2.expandChildren();
//             }
//             CHC::Compose(a0) => {
//                 a0.expandChildren();
//             }
//             CHC::True() => {}
//             CHC::False() => {}
//             CHC::BiNode(a0, a1, a2) => {
//                 a0.expandChildren();
//                 a1.expandChildren();
//                 a2.expandChildren();
//             }
//             CHC::Leaf() => {}
//             CHC::And(a0) => {
//                 a0.expandChildren();
//             }
//             CHC::Geq(a0, a1) => {
//                 a0.expandChildren();
//                 a1.expandChildren();
//             }
//             CHC::Leq(a0, a1) => {
//                 a0.expandChildren();
//                 a1.expandChildren();
//             }
//             CHC::Less(a0, a1) => {
//                 a0.expandChildren();
//                 a1.expandChildren();
//             }
//             CHC::Greater(a0, a1) => {
//                 a0.expandChildren();
//                 a1.expandChildren();
//             }
//             CHC::Eq(a0, a1) => {
//                 a0.expandChildren();
//                 a1.expandChildren();
//             }
//             CHC::Add(a0, a1) => {
//                 a0.expandChildren();
//                 a1.expandChildren();
//             }
//             CHC::Minus(a0, a1) => {
//                 a0.expandChildren();
//                 a1.expandChildren();
//             }
//             CHC::Number(a0) => {
//                 a0.expandChildren();
//             }
//             CHC::ComposeInit(a0, a1, a2, a3) => {
//                 a0.expandChildren();
//                 a1.expandChildren();
//                 a2.expandChildren();
//                 a3.expandChildren();
//             }
//             CHC::PredName(a0) => {
//                 a0.expandChildren();
//             }
//         }
//     }
//     fn shrinkChildren(&mut self) {
//         match self {
//             CHC::Int(a0) => {
//                 a0.shrinkChildren();
//             }
//             CHC::Node(a0) => {
//                 a0.shrinkChildren();
//             }
//             CHC::PredSyntax(a0) => {
//                 a0.shrinkChildren();
//             }
//             CHC::New(a0, a1, a2) => {
//                 a0.shrinkChildren();
//                 a1.shrinkChildren();
//                 a2.shrinkChildren();
//             }
//             CHC::Compose(a0) => {
//                 a0.shrinkChildren();
//             }
//             CHC::True() => {}
//             CHC::False() => {}
//             CHC::BiNode(a0, a1, a2) => {
//                 a0.shrinkChildren();
//                 a1.shrinkChildren();
//                 a2.shrinkChildren();
//             }
//             CHC::Leaf() => {}
//             CHC::And(a0) => {
//                 a0.shrinkChildren();
//             }
//             CHC::Geq(a0, a1) => {
//                 a0.shrinkChildren();
//                 a1.shrinkChildren();
//             }
//             CHC::Leq(a0, a1) => {
//                 a0.shrinkChildren();
//                 a1.shrinkChildren();
//             }
//             CHC::Less(a0, a1) => {
//                 a0.shrinkChildren();
//                 a1.shrinkChildren();
//             }
//             CHC::Greater(a0, a1) => {
//                 a0.shrinkChildren();
//                 a1.shrinkChildren();
//             }
//             CHC::Eq(a0, a1) => {
//                 a0.shrinkChildren();
//                 a1.shrinkChildren();
//             }
//             CHC::Add(a0, a1) => {
//                 a0.shrinkChildren();
//                 a1.shrinkChildren();
//             }
//             CHC::Minus(a0, a1) => {
//                 a0.shrinkChildren();
//                 a1.shrinkChildren();
//             }
//             CHC::Number(a0) => {
//                 a0.shrinkChildren();
//             }
//             CHC::ComposeInit(a0, a1, a2, a3) => {
//                 a0.shrinkChildren();
//                 a1.shrinkChildren();
//                 a2.shrinkChildren();
//                 a3.shrinkChildren();
//             }
//             CHC::PredName(a0) => {
//                 a0.shrinkChildren();
//             }
//         }
//     }
//     fn sorted(&self) -> Self {
//         match self {
//             CHC::Int(a0) => CHC::Int(a0.sorted()),
//             CHC::Node(a0) => CHC::Node(a0.sorted()),
//             CHC::PredSyntax(a0) => CHC::PredSyntax(a0.sorted()),
//             CHC::New(a0, a1, a2) => CHC::New(a0.sorted(), a1.sorted(), a2.sorted()),
//             CHC::Compose(a0) => CHC::Compose(a0.sorted()),
//             CHC::True() => CHC::True(),
//             CHC::False() => CHC::False(),
//             CHC::BiNode(a0, a1, a2) => CHC::BiNode(a0.sorted(), a1.sorted(), a2.sorted()),
//             CHC::Leaf() => CHC::Leaf(),
//             CHC::And(a0) => CHC::And(a0.sorted()),
//             CHC::Geq(a0, a1) => CHC::Geq(a0.sorted(), a1.sorted()),
//             CHC::Leq(a0, a1) => CHC::Leq(a0.sorted(), a1.sorted()),
//             CHC::Less(a0, a1) => CHC::Less(a0.sorted(), a1.sorted()),
//             CHC::Greater(a0, a1) => CHC::Greater(a0.sorted(), a1.sorted()),
//             CHC::Eq(a0, a1) => CHC::Eq(a0.sorted(), a1.sorted()),
//             CHC::Add(a0, a1) => CHC::Add(a0.sorted(), a1.sorted()),
//             CHC::Minus(a0, a1) => CHC::Minus(a0.sorted(), a1.sorted()),
//             CHC::Number(a0) => CHC::Number(a0.sorted()),
//             CHC::ComposeInit(a0, a1, a2, a3) => {
//                 CHC::ComposeInit(a0.sorted(), a1.sorted(), a2.sorted(), a3.sorted())
//             }
//             CHC::PredName(a0) => CHC::PredName(a0.sorted()),
//         }
//     }
// }
