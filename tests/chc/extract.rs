use std::collections::{BTreeMap, BTreeSet};

use rand::{rngs::StdRng, seq::SliceRandom, Rng, SeedableRng};

use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RandomExtractError {
    EmptyEClass(Id),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RandomExtract {
    pub root: Id,
    pub chosen: BTreeMap<Id, CHC>,
}

pub fn random_extract(
    root: &AppliedId,
    eg: &CHCEGraph,
) -> Result<RandomExtract, RandomExtractError> {
    let mut rng = rand::thread_rng();
    random_extract_with_rng(root, eg, &mut rng)
}

pub fn random_extract_from_eclass(
    id: Id,
    eg: &CHCEGraph,
) -> Result<RandomExtract, RandomExtractError> {
    random_extract(&AppliedId::new(id, SlotMap::identity(eg.slots(id))), eg)
}

pub fn random_extract_with_rng<R: Rng + ?Sized>(
    root: &AppliedId,
    eg: &CHCEGraph,
    rng: &mut R,
) -> Result<RandomExtract, RandomExtractError> {
    let root = eg.find_applied_id(root);

    if eg.enodes(root.id).is_empty() {
        return Err(RandomExtractError::EmptyEClass(root.id));
    }

    let mut chosen = BTreeMap::new();
    random_extract_impl(root.id, eg, rng, &mut chosen)?;

    Ok(RandomExtract {
        root: root.id,
        chosen,
    })
}

pub fn selected_eclass_count(extract: &RandomExtract) -> usize {
    extract.chosen.len()
}

fn random_extract_impl<R: Rng + ?Sized>(
    root: Id,
    eg: &CHCEGraph,
    rng: &mut R,
    chosen: &mut BTreeMap<Id, CHC>,
) -> Result<(), RandomExtractError> {
    if chosen.contains_key(&root) {
        return Ok(());
    }

    let mut candidates: Vec<CHC> = eg.enodes(root).into_iter().collect();
    if candidates.is_empty() {
        return Err(RandomExtractError::EmptyEClass(root));
    }
    candidates.shuffle(rng);

    let enode = candidates.into_iter().next().unwrap();
    let child_ids: Vec<Id> = enode
        .applied_id_occurrences()
        .into_iter()
        .map(|app| app.id)
        .collect();
    chosen.insert(root, enode);

    for child in child_ids {
        random_extract_impl(child, eg, rng, chosen)?;
    }

    Ok(())
}

pub fn assert_random_extract_is_closed(extract: &RandomExtract, eg: &CHCEGraph) {
    assert!(extract.chosen.contains_key(&extract.root));

    for (id, enode) in &extract.chosen {
        let app = eg
            .lookup(enode)
            .expect("selected enode should still exist in the e-graph");
        assert_eq!(eg.find_applied_id(&app).id, *id);

        for child in enode.applied_id_occurrences() {
            assert!(
                extract.chosen.contains_key(&child.id),
                "selected enode in {id} references unselected child class {}",
                child.id
            );
        }
    }
}

#[test]
fn random_extractor_returns_closed_selection() {
    initLogger();

    let mut eg = CHCEGraph::default();
    growEGraph("tests/chc/cases/leaf_drop.txt", &mut eg);
    eg.rebuild();

    let mut rng = StdRng::seed_from_u64(0);
    for id in eg.ids() {
        let root = AppliedId::new(id, SlotMap::identity(eg.slots(id)));
        let Ok(extract) = random_extract_with_rng(&root, &eg, &mut rng) else {
            continue;
        };

        if selected_eclass_count(&extract) <= 1 {
            continue;
        }

        assert_random_extract_is_closed(&extract, &eg);
        assert_eq!(extract.root, id);
        return;
    }

    panic!("failed to find a non-trivial CHC class that the random extractor could select");
}
