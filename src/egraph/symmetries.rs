use crate::*;
use log::{debug, info, trace, warn};
use rustsat::encodings::CollectClauses;
use rustsat::instances::{BasicVarManager, SatInstance};
use rustsat::solvers::{Solve, SolverResult};
use rustsat::types::{Clause, Lit, TernaryVal};
use rustsat_minisat::core::Minisat;

use std::collections::BTreeSet;
use std::{collections::BTreeMap, os::raw::c_int};

fn dnfToCnfByTseitin(dnf: &Vec<Vec<isize>>, count: &mut isize) -> Vec<Vec<isize>> {
    if dnf.is_empty() {
        return vec![vec![]];
    }

    // True: any clause is empty (empty conjunction = true)
    for clause in dnf {
        if clause.is_empty() {
            return vec![];
        }
    }

    let mut cnf = Vec::new();
    let mut clause_vars = Vec::new(); // will hold the fresh variable for each DNF clause

    for clause in dnf {
        let fresh_var: isize = (*count).try_into().unwrap();
        *count += 1;
        clause_vars.push(fresh_var);

        // (fresh_var → each literal)   i.e., not fresh_var or lit
        for &lit in clause {
            cnf.push(vec![-fresh_var, lit]);
        }

        // (each literal → fresh_var)   i.e., fresh_var or not lit1 or lit2 or ...
        let mut reverse = vec![fresh_var];
        // not lit1 or lit2 or ...
        reverse.extend(clause.iter().map(|&lit| -lit));
        cnf.push(reverse);
    }

    // At least one DNF clause must be true: (fresh₁ ∨ fresh₂ ∨ ... ∨ freshₘ)
    cnf.push(clause_vars);

    cnf
}

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    fn symmetriesBySat(self: &mut EGraph<L, N>, src_id: Id) -> (Vec<SlotMap>, Id) {
        info!("symmetriesBySat {:?}", src_id);
        let pc1 = self.pc_from_src_id(src_id);
        let childrenType = pc1.node.elem.getChildrenType();
        if childrenType.contains(&LanguageChildrenType::Bind) {
            warn!("change to orig {:?}", src_id);
            return self.orig_determine_self_symmetries(src_id);
        }

        let mut instance: SatInstance<BasicVarManager> = SatInstance::new();

        trace!("pc1 node {:?}", pc1.node.elem);
        let appIds = pc1.node.elem.applied_id_occurrences();
        trace!("pc1 appIds {:?}", appIds);
        if appIds.len() == 0 {
            let publicSlots = pc1.node.elem.public_slot_occurrences();
            return (
                vec![SlotMap::identity(&publicSlots.into())],
                pc1.target_id(),
            );
        }

        let mut slotsIdx = BTreeMap::new();
        // s -> appId, position arg
        let mut slotsPos = BTreeMap::new();
        for (i, appId) in appIds.iter().enumerate() {
            for (j, (_, s)) in appId.m.iter().enumerate() {
                if !slotsIdx.contains_key(&s) {
                    slotsIdx.insert(s, slotsIdx.len());
                }
                slotsPos.entry(s).or_insert(vec![]).push((i, j));
            }
        }

        // TODO: should we change this to vec for faster?
        // at[i][j][s] is true iff slot s is positioned at j in the i-th appId
        let mut at: BTreeMap<(usize, usize, &Slot), isize> = BTreeMap::new();
        // must start at 1 because we use negation for false
        let mut nextId: isize = 1;
        for (i, appId) in appIds.iter().enumerate() {
            for j in 0..appId.m.len() {
                for s in slotsIdx.keys() {
                    at.insert((i, j, s), nextId);
                    nextId += 1;
                }
            }
        }

        // index into permSlots is determined by SlotIdx
        // permSlots[x][y] is true iff x is mapped to y
        let mut permSlots = vec![vec![0; slotsIdx.len()]; slotsIdx.len()];
        for i in 0..permSlots.len() {
            for j in 0..permSlots[i].len() {
                permSlots[i][j] = nextId;
                nextId += 1;
            }
        }

        // perm1 or perm2 or ...
        for (i, appId) in appIds.iter().enumerate() {
            trace!("add var for appId {appId:?}");
            let perms: Vec<_> = self.classes[&appId.id]
                .group()
                .all_perms()
                .into_iter()
                .collect();
            let mut dnf: Vec<Vec<isize>> = Vec::new();
            for perm in perms {
                trace!("perm {perm:?}");
                let newSlotmap = perm.elem.compose(&appId.m);
                let mut dnfClause: Vec<isize> = Vec::new();
                dnfClause.reserve(newSlotmap.len());

                trace!("dnf: ");
                for (j, (_, to)) in newSlotmap.iter().enumerate() {
                    trace!("at({i}, {j}, {to})");
                    dnfClause.push(at[&(i, j, &to)]);
                }

                // if y replace x positionally then permSlots[x][y] must be true
                for (from, origTo) in appId.m.iter() {
                    let newTo = newSlotmap[from];
                    trace!("permSlots[{origTo}][{newTo}]");
                    dnfClause.push(permSlots[slotsIdx[&origTo]][slotsIdx[&newTo]]);
                }

                dnf.push(dnfClause);
            }

            trace!("dnf {dnf:?}");

            for cnfClause in dnfToCnfByTseitin(&dnf, &mut nextId) {
                let cnfClause: Vec<_> = cnfClause
                    .into_iter()
                    .map(|x| Lit::new(x.abs() as u32, x < 0))
                    .collect();
                instance.add_clause(cnfClause.as_slice().into());
            }
        }

        // TODO: we must add a few more conditions
        // 1) if x replaces y (permSlots[x][y] == true), then y at previous positional occurrence of x must be true
        for (x, i) in slotsIdx.iter() {
            for (y, j) in slotsIdx.iter() {
                if i == j {
                    continue;
                }
                // if permSlots[x][y] then y at previous positional occurrence of x must be true
                trace!("if permSlots[{x}][{y}] then");
                // not permSlots[x][y] or (y at previous positional occurrence of x must be true)
                let mut clause = vec![Lit::negative(permSlots[slotsIdx[&x]][slotsIdx[&y]] as u32)];
                for (appIdIdx, posIdx) in slotsPos[&x].iter() {
                    trace!("at[{appIdIdx}, {posIdx}, {y}]");
                    clause.push(Lit::positive(
                        at[&(*appIdIdx, *posIdx, y)].try_into().unwrap(),
                    ));
                }
                instance.add_clause(clause.as_slice().into());
            }
        }

        // 2) (is this necessary?), position must be bijection. E.g. if a takes the ith position, then others must not take the ith position
        for ((i, j, s), idx) in at.iter() {
            trace!("if at[{i}, {j}, {s}] then");
            for s2 in slotsIdx.keys() {
                trace!("not at[{i}, {j}, {s2}]");
                if s2 == *s {
                    continue;
                }
                instance.add_clause(
                    vec![
                        Lit::negative(*idx as u32),
                        Lit::negative(at[&(*i, *j, s2)].try_into().unwrap()),
                    ]
                    .as_slice()
                    .into(),
                );
            }
        }

        // 3) (is this necessary?), permSlots must be bijection. E.g. if x is permuted to y, then others cannot permute to y
        for (_, i) in slotsIdx.iter() {
            for (y, j) in slotsIdx.iter() {
                trace!("if permSlots[{i}][{y}] then");
                for (z, k) in slotsIdx.iter() {
                    if y == z {
                        continue;
                    }
                    trace!("not permSlots[{i}][{z}]");
                    instance.add_clause(
                        vec![
                            Lit::negative(permSlots[*i][*j] as u32),
                            Lit::negative(permSlots[*i][*k] as u32),
                        ]
                        .as_slice()
                        .into(),
                    );
                }
            }
        }

        let enodeAppIdMapInverse = pc1.pai.elem.m.inverse();
        let eclassId = pc1.target_id();
        let mut solver = Minisat::default();
        solver.add_cnf(instance.into_cnf().0).unwrap();
        let mut allPerms = vec![];
        while solver.solve().unwrap() == SolverResult::Sat {
            let mut perm = SlotMap::new();
            let sol = solver.full_solution().unwrap();
            for (x, i) in slotsIdx.iter() {
                for (y, j) in slotsIdx.iter() {
                    match sol[Lit::positive(permSlots[*i][*j] as u32).var()] {
                        TernaryVal::True => {
                            assert!(!perm.contains_key(*x));
                            perm.insert(x.clone(), y.clone());
                        }
                        TernaryVal::False => {}
                        _ => {}
                    }
                }
            }

            let mut normalizedPerm = SlotMap::new();
            for (x, y) in perm.iter() {
                if enodeAppIdMapInverse.contains_key(x) {
                    normalizedPerm.insert(
                        enodeAppIdMapInverse[x.clone()],
                        enodeAppIdMapInverse[y.clone()],
                    );
                }
            }
            allPerms.push(normalizedPerm);

            let mut blocking: Vec<Lit> = Vec::new();
            for lit in sol.iter() {
                match sol[lit.var()] {
                    TernaryVal::True => blocking.push(Lit::negative(lit.vidx32())),
                    TernaryVal::False => blocking.push(Lit::positive(lit.vidx32())),
                    _ => {
                        panic!()
                    }
                }
            }

            rustsat::solvers::Solve::add_clause(&mut solver, blocking.as_slice().into()).unwrap();
        }

        info!("done symmetriesBySat {:?}", src_id);
        (allPerms, eclassId)
    }

    pub(crate) fn determine_self_symmetries(&mut self, src_id: Id) {
        let (allPerms, i) = self.symmetriesBySat(src_id);

        if CHECKS {
            let (allPerms2, i2) = self.orig_determine_self_symmetries(src_id);
            let allPermSet = allPerms.iter().collect::<BTreeSet<_>>();
            let allPermSet2 = allPerms2.iter().collect::<BTreeSet<_>>();
            assert_eq!(allPermSet, allPermSet2);
            assert_eq!(i, i2);
        }

        // should be the place that updates this group permutation if children eclasses are permuted

        for perm in allPerms {
            // TODO: why cant we put grp outside this scope?
            let grp = self.classes.get_mut(&i).unwrap().groupMut();

            if grp.add(ProvenPerm { elem: perm }) {
                self.touched_class(i, PendingType::Full);
            }
        }
    }

    // finds self-symmetries caused by the e-node `src_id`.
    fn orig_determine_self_symmetries(&mut self, src_id: Id) -> (Vec<SlotMap>, Id) {
        // get smallest weak shape of syn node
        trace!("call orig_determine_self_symmetries {:?}", src_id);
        let pc1 = self.pc_from_src_id(src_id);

        let i = pc1.target_id();
        let weak = pc1.node.elem.weak_shape().0;
        trace!("pc1 node {:?}", pc1.node.elem);
        trace!("pc1 appId {:?}", pc1.pai.elem);

        let mut allPerms = vec![];
        for pn2 in self.proven_proven_get_group_compatible_variants(&pc1.node) {
            trace!("pc2 {:?}", pn2.elem);
            let pc2 = ProvenContains {
                pai: pc1.pai.clone(),
                node: pn2,
            };
            let (weak2, _) = pc2.node.elem.weak_shape();
            if weak == weak2 {
                if CHECKS {
                    self.check_pc(&pc1);
                }
                if CHECKS {
                    self.check_pc(&pc2);
                }
                if CHECKS {
                    assert_eq!(pc1.target_id(), pc2.target_id());
                }

                #[allow(unused)]
                let (a, b, proof) = self.pc_congruence(&pc1, &pc2);

                // or is it the opposite direction? (flip a with b)
                trace!("a {a:?}");
                trace!("b {b:?}");
                trace!("eclass {:?}", self.eclass(a.id).unwrap());
                trace!("pc1 {pc1:?}");
                trace!("pc2 {pc2:?}");
                let perm = a.m.compose(&b.m.inverse());

                // let proven_perm = ProvenPerm {
                //     elem: perm,

                //     #[cfg(feature = "explanations")]
                //     proof,

                //     #[cfg(feature = "explanations")]
                //     reg: self.proof_registry.clone(),
                // };

                if CHECKS {
                    perm.check();
                }

                trace!("add perm {perm:?}");
                allPerms.push(perm);
            }
        }

        trace!("done orig_determine_self_symmetries {:?}", src_id);
        (allPerms, i)
    }
}
