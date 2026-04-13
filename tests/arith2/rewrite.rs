use crate::*;
pub fn get_all_rewrites2() -> Vec<Rewrite<Arith2>> {
    vec![
        add_comm(),
        add_assoc1(),
        add_assoc2(),
        add_long(),
        add_long_expand(),
        add_long_sort(),
    ]
}

pub fn add_comm() -> Rewrite<Arith2> {
    let pat = "(add ?a ?b)";
    let outpat = "(add ?b ?a)";
    Rewrite::new("add-comm", pat, outpat)
}

fn add_assoc1() -> Rewrite<Arith2> {
    let pat = "(add ?a (add ?b ?c))";
    let outpat = "(add (add ?a ?b) ?c)";
    Rewrite::new("add-assoc1", pat, outpat)
}

fn add_assoc2() -> Rewrite<Arith2> {
    let pat = "(add (add ?a ?b) ?c)";
    let outpat = "(add ?a (add ?b ?c))";
    Rewrite::new("add-assoc2", pat, outpat)
}

fn add_long() -> Rewrite<Arith2> {
    let pat = "(add ?a ?b)";
    let outpat = "(addLong <?a ?b>)";
    Rewrite::new("add-long", pat, outpat)
}

fn add_long_expand() -> Rewrite<Arith2> {
    let pat = "(addLong <(add ?a ?b) *0>)";
    RewriteT {
        name: "add-long-expand".to_owned(),
        searcher: Box::new(move |eg| ematch_all(eg, &Pattern::parse(pat).unwrap())),
        applier: Box::new(move |substs: Vec<(Subst, AppliedId)>, eg| {
            for (subst, rootAppId) in substs {
                let a = subst["a"].clone();
                let b = subst["b"].clone();

                let prevAddAppId = eg.lookup(&Arith2::Add(a.clone(), b.clone())).unwrap();
                let mut prevAddLongChildren = vec![prevAddAppId.clone()];

                let mut newAddLongChildren = vec![
                    AppliedIdOrStar::AppliedId(a.clone()),
                    AppliedIdOrStar::AppliedId(b.clone()),
                ];
                let mut star0Count = 0;
                while subst.contains_key(&format!("star_0_{}", star0Count)) {
                    prevAddLongChildren.push(subst[&format!("star_0_{}", star0Count)].clone());
                    newAddLongChildren.push(AppliedIdOrStar::AppliedId(
                        subst[&format!("star_0_{}", star0Count)].clone(),
                    ));
                    star0Count += 1;
                }

                let newAddLong = eg.add(&Arith2::AddLong(newAddLongChildren.into()));

                // println!("rootAppId {rootAppId:?}");
                // println!("newAddLong {newAddLong:?}");

                eg.union(&rootAppId, &newAddLong);
            }
        }),
    }
    .into()
}

fn add_long_sort() -> Rewrite<Arith2> {
    let pat = "(addLong <(add ?a ?b) *0>)";
    RewriteT {
        name: "add-long-sort".to_owned(),
        searcher: Box::new(move |eg| {}),
        applier: Box::new(move |(), eg| {
            let ids = eg.ids();

            for id in ids {
                // if see addLong, then shuffle the children
                let appId = eg.mk_identity_applied_id(id);
                let enodes = eg.enodes(id);
                for enode in enodes {
                    let Arith2::AddLong(mut children) = enode else {
                        continue;
                    };

                    let permuteChildren = permute_iter(&children);

                    for mut children in permuteChildren {
                        children.sort();

                        let newENode = Arith2::AddLong(children.into());
                        let newENodeId = eg.add(&newENode);
                        eg.union(&appId, &newENodeId);
                    }
                }
            }
        }),
    }
    .into()
}

// fn add_long_expand() -> Rewrite<Arith2> {
//     let searcher = Box::new(|_eg: &EGraph<Arith2>| -> () {});
//     let applier = Box::new(|_: (), eg: &mut EGraph<Arith2>| {
//         let eclasses = eg.ids();
//         for eclassId in eclasses {
//             let eclass = eg.eclass(eclassId).unwrap();

//             let (enodesList, origENodeAppId) = {
//                 let egRead = getEg(eg);
//                 let eclassId = egRead.find_id(eclassId);
//                 let origENodeAppId = egRead.mk_identity_applied_id(eclassId);

//                 (egRead.enodes(origENodeAppId.id), origENodeAppId)
//             };
//         }
//     });
//     RewriteT {
//         name: "add-long-expand".to_owned(),
//         searcher,
//         applier,
//     }
//     .into()
// }
