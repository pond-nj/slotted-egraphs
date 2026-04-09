use crate::*;
pub fn get_all_rewrites2() -> Vec<Rewrite<Arith2>> {
    vec![
        add_comm(),
        add_assoc1(),
        add_assoc2(),
        add_long(),
        add_long_expand(),
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
        applier: Box::new(move |substs: Vec<(Subst, Id)>, eg| {
            for (subst, rootId) in substs {
                let a = subst["a"].clone();
                let b = subst["b"].clone();

                let prevAddAppId = eg.lookup(&Arith2::Add(a.clone(), b.clone())).unwrap();
                let mut prevAddLongChildren = vec![AppliedIdOrStar::AppliedId(prevAddAppId)];

                let mut newAddLongChildren = vec![
                    AppliedIdOrStar::AppliedId(a.clone()),
                    AppliedIdOrStar::AppliedId(b.clone()),
                ];
                let mut star0Count = 0;
                while subst.contains_key(&format!("star_0_{}", star0Count)) {
                    prevAddLongChildren.push(AppliedIdOrStar::AppliedId(
                        subst[&format!("star_0_{}", star0Count)].clone(),
                    ));
                    newAddLongChildren.push(AppliedIdOrStar::AppliedId(
                        subst[&format!("star_0_{}", star0Count)].clone(),
                    ));
                    star0Count += 1;
                }

                let newAddLong = eg.add(&Arith2::AddLong(newAddLongChildren.into()));
                let rootAppId = eg
                    .lookup(&Arith2::AddLong(prevAddLongChildren.into()))
                    .unwrap();
                eg.union(&rootAppId, &newAddLong);
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
