use crate::*;
use log::{debug, trace};
use rustsat::encodings::CollectClauses;
use rustsat::instances::SatInstance;
use rustsat::solvers::Solve;
use rustsat::types::{Clause, Lit};
use rustsat_minisat::core::Minisat;

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
    pub(crate) fn determine_self_symmetries(&mut self, src_id: Id) {
        let pc1 = self.pc_from_src_id(src_id);
        let childrenType = pc1.node.elem.getChildrenType();
        if childrenType.contains(&LanguageChildrenType::Bind) {
            self.orig_determine_self_symmetries(src_id);
            return;
        }

        let mut instance = SatInstance::new();
        let appIds = pc1.node.elem.applied_id_occurrences();

        let mut slotsIdx = BTreeMap::new();
        let mut slotsPos = BTreeMap::new();
        for (i, appId) in appIds.iter().enumerate() {
            for (j, (_, s)) in appId.m.iter().enumerate() {
                if !slotsIdx.contains_key(&s) {
                    slotsIdx.insert(*s, slotsIdx.len());
                }
                slotsPos.entry(*s).or_insert(vec![]).push((i, j));
            }
        }

        // TODO: should we change this to vec for faster?
        // vars[i][j][s] is true iff slot s is positioned at j in the i-th appId
        let mut vars: BTreeMap<(usize, usize, &Slot), isize> = BTreeMap::new();
        // must start at 1 because we use negation for false
        let mut nextId: isize = 1;
        for (i, appId) in appIds.iter().enumerate() {
            for j in 0..appId.m.len() {
                for s in slots.iter() {
                    vars.insert((i, j, s), nextId);
                    nextId += 1;
                }
            }
        }

        // permSlots[x][y] is true iff x is mapped to y
        let mut permSlots = vec![vec![0; slots.len()]; slots.len()];
        for i in 0..permSlots.len() {
            for j in 0..permSlots[i].len() {
                permSlots[i][j] = nextId;
                nextId += 1;
            }
        }

        // perm1 or perm2 or ...
        for (i, appId) in appIds.iter().enumerate() {
            let perms: Vec<_> = self.classes[&appId.id]
                .group()
                .all_perms()
                .into_iter()
                .collect();
            let mut dnf: Vec<Vec<isize>> = Vec::new();
            for perm in perms {
                let newSlotmap = perm.elem.compose(&appId.m);
                let mut dnfClause: Vec<isize> = Vec::new();
                dnfClause.reserve(newSlotmap.len());

                for (j, (_, to)) in newSlotmap.iter().enumerate() {
                    dnfClause.push(vars[&(i, j, &to)]);
                }

                // if y replace x positionally then permSlots[x][y] must be true
                for (from, origTo) in appId.m {
                    let newTo = newSlotmap[&from];
                    dnfClause.push(permSlots[&slotsIdx[origTo]][&slotsIdx[newTo]]);
                }

                dnf.push(dnfClause);
            }
            for cnf in dnfToCnfByTseitin(&dnf, &mut nextId) {
                let cnf: Vec<_> = cnf.into_iter().map(|x| Lit::new(x, x > 0)).collect();
                instance.add_clause(cnf.as_slice().into());
            }
        }

        // TODO: we must add a few more conditions
        // 1) if x replaces y (permSlots[x][y] == true), then y at previous positional occurrence of x must be true
        for i in 0..permSlots.len() {
            for j in 0..permSlots[i].len() {
                // if permSlots[x][y] then y at previous positional occurrence of x must be true
                // not permSlots[x][y] or (y at previous positional occurrence of x must be true)
            }
        }
        // 2) (is this necessary?), position must be bijection. E.g. if a takes the ith position, then others must not take the ith position
        // 3) (is this necessary?), permSlots must be bijection. E.g. if x is permuted to y, then others cannot permute to y

        let mut solver = Minisat::default();
        solver.add_instance(&instance).unwrap();
    }

    // finds self-symmetries caused by the e-node `src_id`.
    fn orig_determine_self_symmetries(&mut self, src_id: Id) {
        // get smallest weak shape of syn node
        let pc1 = self.pc_from_src_id(src_id);

        let i = pc1.target_id();
        let weak = pc1.node.elem.weak_shape().0;
        trace!("pc1 node {:?}", pc1.node.elem);
        trace!("pc1 appId {:?}", pc1.pai.elem);
        for pn2 in self.proven_proven_get_group_compatible_variants(&pc1.node) {
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
                let perm = a.m.compose(&b.m.inverse());

                let proven_perm = ProvenPerm {
                    elem: perm,

                    #[cfg(feature = "explanations")]
                    proof,

                    #[cfg(feature = "explanations")]
                    reg: self.proof_registry.clone(),
                };

                if CHECKS {
                    proven_perm.check();
                }
                // should be the place that updates this group permutation if children eclasses are permuted
                let grp = self.classes.get_mut(&i).unwrap().groupMut();
                if grp.add(proven_perm) {
                    self.touched_class(i, PendingType::Full);
                }
            }
        }
    }
}
