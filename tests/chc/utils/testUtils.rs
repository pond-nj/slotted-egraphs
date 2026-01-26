use super::*;

#[macro_export]
macro_rules! checkRes {
    ($keyword: expr, $res:expr) => {
        assert!(
            $res.len() > 0,
            "{} is empty, expected at least one element.",
            $keyword
        );

        let allIds = $res.iter().map(|x| &x.1).collect::<BTreeSet<_>>();

        assert!(
            allIds.len() == 1,
            "Expected all elements to have the same ID. Found IDs: {:?}",
            allIds
        );
    };
}

pub fn checkSelfCycle(eg: &CHCEGraph) {
    'idloop: for composeId in eg.ids() {
        let composeENodes = eg.enodes(composeId);
        for composeENode in composeENodes {
            match composeENode {
                CHC::Compose(children) => {
                    if children.len() != 1 {
                        continue;
                    }

                    let AppliedIdOrStar::AppliedId(child) = &children[0] else {
                        panic!();
                    };

                    for newENode in eg.enodes(child.id) {
                        let CHC::New(syntax, constr, predChildren) = newENode else {
                            panic!();
                        };

                        if predChildren.len() != 1 {
                            continue;
                        }

                        assert_ne!(predChildren[0].getAppliedId().id, composeId);
                    }
                }
                CHC::ComposeInit(..) => {
                    continue;
                }
                _ => continue 'idloop,
            }
        }
    }
}
