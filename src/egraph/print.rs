use super::*;
use crate::*;
use std::{collections::BTreeMap, fmt};

impl<L: Language, N: Analysis<L>> EClass<L, N> {
    pub fn dumpEClass<T: fmt::Write>(&self, f: &mut T) -> Result {
        // if self.nodes.len() == 0 {
        //     write!(f, "\n Empty Eclass")?;
        //     return Ok(());
        // }

        let mut slot_order: Vec<Slot> = self.slots.iter().cloned().collect();
        slot_order.sort();
        let slot_str = slot_order
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "\n{:?}", self.analysis_data)?;
        write!(f, "\n({}):", &slot_str)?;

        write!(f, ">> {:?}\n", &self.syn_enode())?;

        for (sh, psn) in &self.nodes {
            let node = sh.apply_slotmap(&psn.elem);

            #[cfg(feature = "explanations")]
            write!(f, " - {n:?}    [originally {:?}]", psn.src_id);

            #[cfg(not(feature = "explanations"))]
            write!(f, " - {node:?}\n")?;
            write!(f, " >- {sh:?}\n")?;
        }
        for pp in &self.group().generators() {
            write!(f, " -- {:?}\n", pp.elem)?;
        }

        Ok(())
    }

    pub fn dumpEClassEG<T: fmt::Write>(
        &self,
        f: &mut T,
        i: Id,
        map: &mut BTreeMap<AppliedId, RecExpr<L>>,
        calls: &mut BTreeMap<Id, usize>,
        eqvIds: &BTreeMap<Id, Vec<Id>>,
        eg: &EGraph<L, N>,
    ) -> Result {
        if self.nodes.len() == 0 {
            return Ok(());
        }

        let slot_order: Vec<Slot> = self.slots().into();
        let slot_str = slot_order
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        let synExpr = eg.getSynExpr(&i, map, calls);
        if synExpr.is_err() {
            write!(f, "\n{}", synExpr.unwrap_err())?;
        } else {
            write!(f, "\n{}", synExpr.unwrap())?;
        }

        write!(f, "\n{:?}", self.analysis_data)?;
        write!(f, "\n{:?}({:?})({}):\n", i, eqvIds[&i], &slot_str)?;
        write!(f, ">> {:?}\n", eg.getSynNodeNoSubst(&i))?;

        let mut eclassNodes: Vec<_> = eg.enodes(i).into_iter().collect();
        eclassNodes.sort();

        for node in eclassNodes {
            write!(f, " - {node:?}\n")?;
            let (sh, _) = node.weak_shape();
            write!(f, " -   {sh:?}\n")?;
        }
        let permute = eg.getSlotPermutation(&i);
        write!(f, "permute len {}\n", permute.len())?;
        for p in permute {
            write!(f, " -- {:?}\n", p)?;
        }

        Ok(())
    }

    pub fn slots(&self) -> SmallHashSet<Slot> {
        self.slots.clone()
    }
}

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    pub fn dump<T: fmt::Write>(&self, f: &mut T) -> Result {
        write!(f, "\n == Egraph ==")?;
        write!(f, "\n size of egraph: {}", self.total_number_of_nodes())?;
        let mut eclasses = self.ids();
        eclasses.sort();

        let eqvIds = self.buildEqvIds();

        let mut map = BTreeMap::<AppliedId, RecExpr<L>>::default();
        let mut calls = BTreeMap::new();
        for i in eclasses {
            self.eclass(i)
                .unwrap()
                .dumpEClassEG(f, i, &mut map, &mut calls, &eqvIds, self)?;
        }

        Ok(())
    }

    pub fn printUnionFind(&self) {
        let uf = &self.unionfind;
        println!("unionfind info:");
        println!("unionfind size {}", uf.borrow().len());
        for (i, x) in uf.borrow().iter().enumerate() {
            println!("Id{i:?} -> {:?}", x.elem);
        }
    }
}
