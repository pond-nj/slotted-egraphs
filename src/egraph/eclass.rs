use super::*;

/// Each E-Class can be understood "semantically" or "syntactically":
/// - semantically means that it respects the equations already in the e-graph, and hence doesn't differentiate between equal things.
/// - syntactically means that it only talks about the single representative term associated to each E-Class, recursively obtainable using syn_enode.
pub struct EClass<L: Language, N: Analysis<L>> {
    // The set of equivalent ENodes that make up this eclass.
    // for (sh, bij) in nodes; sh.apply_slotmap(bij) represents the actual ENode.
    #[cfg(not(feature = "parallelAdd"))]
    pub nodes: BTreeMap<ENodeId, ProvenSourceNode>,

    #[cfg(feature = "parallelAdd")]
    pub nodes: BTreeMap<ENodeId, ProvenSourceNode>,

    // All other slots are considered "redundant" (or they have to be qualified by a ENode::Lam).
    // Should not contain Slot(0).
    pub slots: SmallHashSet<Slot>,

    // Shows which Shapes refer to this EClass.
    usages: BTreeSet<ENodeId>,

    // Expresses the self-symmetries of this e-class.
    group: Group<ProvenPerm>,

    // TODO remove this if explanations are disabled.
    syn_enode: L,

    pub analysis_data: N::Data,
}

impl<L: Language, N: Analysis<L>> EClass<L, N> {
    pub fn new(
        nodes: BTreeMap<ENodeId, ProvenSourceNode>,
        slots: SmallHashSet<Slot>,
        usages: BTreeSet<ENodeId>,
        group: Group<ProvenPerm>,
        syn_enode: L,
        analysis_data: N::Data,
    ) -> Self {
        Self {
            nodes,
            slots,
            usages,
            group,
            syn_enode,
            analysis_data: analysis_data,
        }
    }

    pub fn group(&self) -> &Group<ProvenPerm> {
        &self.group
    }

    pub fn groupMut(&mut self) -> &mut Group<ProvenPerm> {
        // trace!("modifying group of {:?}", self.syn_enode.orig_weak_shape());
        &mut self.group
    }

    pub fn syn_enode(&self) -> &L {
        &self.syn_enode
    }

    pub fn usages(&self) -> &BTreeSet<ENodeId> {
        &self.usages
    }

    pub fn usagesMut(&mut self) -> &mut BTreeSet<ENodeId> {
        &mut self.usages
    }
}
