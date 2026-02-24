use super::*;

pub fn dumpCHCEClass(
    i: Id,
    map: &mut BTreeMap<AppliedId, RecExpr<CHC>>,
    eqvIds: &BTreeMap<Id, Vec<Id>>,
    eg: &CHCEGraph,
) {
    let nodes = eg.enodes(i);
    if nodes.len() == 0 {
        return;
    }

    let mut slot_order: Vec<Slot> = eg.slots(i).into();
    let mut slot_sorted = slot_order.clone();
    slot_sorted.sort();
    assert!(slot_order == slot_sorted);
    let slot_str = slot_order
        .iter()
        .map(|x| x.to_string())
        .collect::<Vec<_>>()
        .join(", ");

    // TODO: this function uses too much memory
    // let synExpr = eg.getSynExpr(&i, map);
    // print!("\n{}", synExpr);
    print!("\n{:?}", eg.analysis_data(i));
    print!("\n{:?}({:?})({}):", i, eqvIds[&i], &slot_str);
    print!(">> {:?}\n", eg.getSynNodeNoSubst(&i));

    let mut eclassNodes: Vec<_> = eg.enodes(i).into_iter().collect();
    eclassNodes.sort();

    for node in eclassNodes {
        print!(" - {node:?}\n");
        let (sh, m) = node.weak_shape();
        print!(" >-  {sh:?}\n");
        let (sh, m) = weakShapeCHC(&node);
        print!(" - or  {sh:?}\n");
    }
    let permute = eg.getSlotPermutation(&i);
    for p in permute {
        print!(" -- {:?}\n", p);
    }
}

pub fn dumpCHCEGraph(eg: &CHCEGraph) {
    print!("\n == Egraph ==");
    print!("\n size of egraph: {}", eg.total_number_of_nodes());
    let mut eclasses = eg.ids();
    print!("\n number of eclasses: {}", eclasses.len());
    eclasses.sort();

    // TODO: it's possible that map is using too much memory
    let mut map = BTreeMap::<AppliedId, RecExpr<CHC>>::default();
    let eqvIds = eg.buildEqvIds();
    for i in eclasses {
        dumpCHCEClass(i, &mut map, &eqvIds, eg);
    }
    print!("");
}

pub fn printENode(enode: &CHC, eg: &CHCEGraph) {
    // enode can be a newly defined one, it might not exist in the egraph
    let eclassId = eg.lookup(&enode);

    println!("Enode {enode:?}");

    let map = &mut BTreeMap::<AppliedId, RecExpr<CHC>>::default();
    if eclassId.is_some() {
        let eclassId = eclassId.unwrap();
        let calls = &mut BTreeMap::new();
        let synExpr = eg.getSynExpr(&eclassId.id, map, calls).unwrap();
        println!("Inside eclass {eclassId:?}: ");
        println!("{}", synExpr);
    }

    let eqvIds = eg.buildEqvIds();
    println!("child eclass: ");
    for child in enode.applied_id_occurrences() {
        dumpCHCEClass(child.id, map, &eqvIds, eg);
        println!("");
    }
}
