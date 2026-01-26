use super::*;

#[test]
fn mainTest() {
    let mut eg = CHCEGraph::default();
    growEGraph("tests/chc/input/pairing_paper_array.txt", &mut eg);
}
