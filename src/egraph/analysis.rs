use crate::*;

/// E-Graph Analysis allows you to propagate information upwards through the E-Graph.
pub trait Analysis<L: Language>: Sized {
    type Data: Eq + Clone + Debug;
    fn make(eg: &EGraph<L, Self>, enode: &L) -> Self::Data;
    fn merge(l: Self::Data, r: Self::Data, id: Id, eg: &EGraph<L, Self>) -> Self::Data;
    fn modify(_eg: &mut EGraph<L, Self>, _id: Id) {}
}

impl<L: Language> Analysis<L> for () {
    type Data = ();
    fn make(_eg: &EGraph<L, Self>, _: &L) {}
    fn merge(_l: (), _r: (), _id: Id, _eg: &EGraph<L, Self>) -> () {}
}
