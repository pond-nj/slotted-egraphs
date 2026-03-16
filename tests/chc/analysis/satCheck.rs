use super::*;
use z3::{
    ast::{Ast, Bool, Datatype, Int},
    datatype_builder::create_datatypes,
    Config, Context, DatatypeAccessor, DatatypeBuilder, DatatypeSort, SatResult, Solver, Sort,
};

#[derive(Eq, PartialEq, Clone, Debug, Default)]
pub enum SatStatus {
    Sat,
    Unsat,
    #[default]
    Unknown,
}

impl SatStatus {
    pub fn or(&self, other: &SatStatus) -> SatStatus {
        match (self, other) {
            (SatStatus::Sat, _) => SatStatus::Sat,
            (_, SatStatus::Sat) => SatStatus::Sat,
            (SatStatus::Unsat, SatStatus::Unsat) => SatStatus::Unsat,
            _ => SatStatus::Unknown,
        }
    }

    pub fn and(&self, other: &SatStatus) -> SatStatus {
        match (self, other) {
            (SatStatus::Sat, SatStatus::Sat) => SatStatus::Sat,
            (SatStatus::Unsat, _) => SatStatus::Unsat,
            (_, SatStatus::Unsat) => SatStatus::Unsat,
            _ => SatStatus::Unknown,
        }
    }
}

fn returnTypes(enode: &CHC) -> VarType {
    match enode {
        CHC::Number(..) | CHC::Minus(..) | CHC::Add(..) | CHC::IntType(..) => VarType::Int,
        CHC::Leaf() | CHC::BiNode(..) | CHC::NodeType(..) => VarType::Node,
        CHC::ListType(..) | CHC::EmptyList() | CHC::List(..) => VarType::List,
        CHC::Neq(..)
        | CHC::Eq(..)
        | CHC::Greater(..)
        | CHC::Less(..)
        | CHC::Leq(..)
        | CHC::Geq(..)
        | CHC::And(..)
        | CHC::True()
        | CHC::False() => VarType::Bool,
        _ => todo!(),
    }
}

pub struct TypeTree {
    pub thisType: VarType,
    pub childrenType: Vec<TypeTree>,
}

fn buildTypesTree(expr: &RecExpr<CHC>, eg: &CHCEGraph) -> TypeTree {
    let mut childrenType = vec![];
    for child in expr.children.iter() {
        childrenType.push(buildTypesTree(child, eg));
    }

    TypeTree {
        thisType: returnTypes(&expr.node),
        childrenType,
    }
}

#[derive(Debug)]
enum AstWrap {
    Int(Int),
    Bool(Bool),
    List(Datatype),
    Node(Datatype),
}

impl<'ctx> From<AstWrap> for Int {
    fn from(ast: AstWrap) -> Int {
        match ast {
            AstWrap::Int(i) => i,
            other => panic!("expected Int, found {:?}", &other),
        }
    }
}

impl AstWrap {
    pub fn as_int(&self) -> &Int {
        match self {
            AstWrap::Int(ref i) => i,
            _ => panic!("expected Int r variant"),
        }
    }

    pub fn as_bool(&self) -> &Bool {
        match self {
            AstWrap::Bool(ref i) => i,
            _ => panic!("expected Bool r variant"),
        }
    }

    pub fn as_list(&self) -> &Datatype {
        match self {
            AstWrap::List(ref i) => i,
            _ => panic!("expected Datatype r variant"),
        }
    }

    pub fn as_node(&self) -> &Datatype {
        match self {
            AstWrap::Node(ref i) => i,
            _ => panic!("expected Datatype r variant"),
        }
    }
}

pub struct DefineDataTypes {
    pub sorts: Vec<DatatypeSort>,
}

impl DefineDataTypes {
    pub fn new() -> Self {
        let mut sorts = create_datatypes(vec![
            DatatypeBuilder::new("tree")
                .variant("leaf", vec![])
                .variant(
                    "binode",
                    vec![
                        ("data", DatatypeAccessor::Sort(Sort::int())),
                        ("left", DatatypeAccessor::Datatype("tree".into())),
                        ("right", DatatypeAccessor::Datatype("tree".into())),
                    ],
                ),
            DatatypeBuilder::new("list").variant("nil", vec![]).variant(
                "cons",
                vec![
                    ("head", DatatypeAccessor::Sort(Sort::int())),
                    ("tail", DatatypeAccessor::Datatype("list".into())),
                ],
            ),
        ]);

        DefineDataTypes { sorts }
    }

    pub fn get_node(&self) -> &DatatypeSort {
        &self.sorts[0]
    }

    pub fn get_list(&self) -> &DatatypeSort {
        &self.sorts[1]
    }
}

fn buildZ3RecExpr(expr: &RecExpr<CHC>, sorts: &DefineDataTypes, eg: &CHCEGraph) -> AstWrap {
    let mut childrenZ3: Vec<AstWrap> = vec![];
    for child in expr.children.iter() {
        childrenZ3.push(buildZ3RecExpr(child, sorts, eg));
    }

    let retType = returnTypes(&expr.node);
    match retType {
        VarType::Bool => {
            let boolTerms: Bool = match &expr.node {
                CHC::Geq(..) => Int::ge(childrenZ3[0].as_int(), childrenZ3[1].as_int()),
                CHC::Leq(..) => Int::le(childrenZ3[0].as_int(), childrenZ3[1].as_int()),
                CHC::Less(..) => Int::lt(childrenZ3[0].as_int(), childrenZ3[1].as_int()),
                CHC::Greater(..) => Int::gt(childrenZ3[0].as_int(), childrenZ3[1].as_int()),
                CHC::Eq(..) => match childrenZ3[0] {
                    AstWrap::Int(..) => Int::eq(childrenZ3[0].as_int(), childrenZ3[1].as_int()),
                    AstWrap::List(..) => childrenZ3[0].as_list().eq(childrenZ3[1].as_list()),
                    AstWrap::Node(..) => childrenZ3[0].as_node().eq(childrenZ3[1].as_node()),
                    _ => panic!(),
                },
                CHC::Neq(..) => match childrenZ3[0] {
                    AstWrap::Int(..) => Int::ne(childrenZ3[0].as_int(), childrenZ3[1].as_int()),
                    AstWrap::List(..) => childrenZ3[0].as_list().ne(childrenZ3[1].as_list()),
                    AstWrap::Node(..) => childrenZ3[0].as_node().ne(childrenZ3[1].as_node()),
                    _ => panic!(),
                },

                CHC::And(..) => Bool::and(
                    &childrenZ3
                        .iter()
                        .map(|x| x.as_bool())
                        .collect::<Vec<&Bool>>(),
                ),
                CHC::True() => Bool::from_bool(true),
                CHC::False() => Bool::from_bool(false),
                _ => todo!(),
            };
            AstWrap::Bool(boolTerms)
        }
        VarType::Int => {
            let intTerms: Int = match &expr.node {
                CHC::Number(n) => Int::from_u64(*n as u64),
                CHC::Minus(..) => (childrenZ3[0].as_int() - childrenZ3[1].as_int()),
                CHC::Add(..) => childrenZ3[0].as_int() + childrenZ3[1].as_int(),
                CHC::IntType(s) => Int::new_const(s.toStr()),
                _ => todo!(),
            };

            AstWrap::Int(intTerms)
        }
        VarType::List => {
            let listTerms: Datatype = match &expr.node {
                CHC::ListType(s) => Datatype::new_const(s.toStr(), &sorts.get_list().sort),
                CHC::EmptyList() => sorts.get_list().variants[0]
                    .constructor
                    .apply(&[])
                    .as_datatype()
                    .unwrap(),
                CHC::List(head, tail) => sorts.get_list().variants[1]
                    .constructor
                    .apply(&[childrenZ3[0].as_int(), childrenZ3[1].as_list()])
                    .as_datatype()
                    .unwrap(),
                _ => todo!(),
            };
            AstWrap::List(listTerms)
        }
        VarType::Node => {
            let nodeTerms: Datatype = match &expr.node {
                CHC::Leaf() => sorts.get_node().variants[0]
                    .constructor
                    .apply(&[])
                    .as_datatype()
                    .unwrap(),
                CHC::BiNode(x, l, r) => sorts.get_node().variants[1]
                    .constructor
                    .apply(&[
                        childrenZ3[0].as_int(),
                        childrenZ3[1].as_node(),
                        childrenZ3[2].as_node(),
                    ])
                    .as_datatype()
                    .unwrap(),
                CHC::NodeType(s) => Datatype::new_const(s.toStr(), &sorts.get_node().sort),
                _ => todo!(),
            };
            AstWrap::Node(nodeTerms)
        }
        VarType::Unknown => {
            todo!()
        }
    }
}

fn solveZ3Constraint(enode: &CHC, eg: &CHCEGraph) -> SatStatus {
    // println!("doing solving Z3 constraint");

    let CHC::And(..) = enode else {
        panic!();
    };

    let expr = eg.getENodeExpr(enode).unwrap();
    let sorts = DefineDataTypes::new();
    let constraint = buildZ3RecExpr(&expr, &sorts, eg);
    let AstWrap::Bool(constraint) = constraint else {
        panic!();
    };

    let solver = Solver::new();
    // println!("{:?}", constraint);
    solver.assert(&constraint);

    let ret = match solver.check() {
        SatResult::Sat => SatStatus::Sat,
        SatResult::Unsat => SatStatus::Unsat,
        SatResult::Unknown => SatStatus::Unknown,
    };

    // println!("done solving Z3 constraint");
    // println!("result {ret:?}");

    ret
}

pub fn makeSatStatus(enode: &CHC, eg: &CHCEGraph) -> SatStatus {
    if !CHECK_UNSAT_CONSTR {
        return SatStatus::Unknown;
    }

    match enode {
        CHC::True() => SatStatus::Sat,
        CHC::False() => SatStatus::Unsat,
        CHC::And(..) => solveZ3Constraint(enode, eg),
        CHC::Compose(children) => {
            let mut satStatus = SatStatus::Unknown;
            for child in children {
                let child = child.getAppliedId();
                satStatus = satStatus.or(&eg.analysis_data(child.id).satStatus);
                if satStatus == SatStatus::Sat {
                    break;
                }
            }
            satStatus
        }
        CHC::New(_, constr, bodies) => {
            let mut satStatus = SatStatus::Unknown;

            satStatus = satStatus.and(&eg.analysis_data(constr.id).satStatus);
            if satStatus == SatStatus::Unsat {
                return satStatus;
            }

            for body in bodies {
                let body = body.getAppliedId();
                satStatus = satStatus.and(&eg.analysis_data(body.id).satStatus);
                if satStatus == SatStatus::Unsat {
                    return satStatus;
                }
            }

            satStatus
        }
        _ => SatStatus::Unknown,
    }
}

// pub fn satCheckRewrite() -> CHCRewrite {
//     let searcher = Box::new(move |eg: &CHCEGraph| -> Vec<(Id, SatStatus)> {
//         let mut updates = vec![];
//         for eclassId in eg.ids() {
//             if eg.analysis_data(eclassId).satStatus != SatStatus::Unknown {
//                 continue;
//             }

//             let enodes = eg.enodes(eclassId);
//             let firstENode = enodes.iter().next().unwrap();
//             match firstENode {
//                 CHC::True() => {
//                     updates.push((eclassId, SatStatus::Sat));
//                 }
//                 CHC::False() => {
//                     updates.push((eclassId, SatStatus::Unsat));
//                 }
//                 CHC::And(..) => {
//                     updates.push((eclassId, solveZ3Constraint(firstENode, eg)));
//                 }
//                 _ => {}
//             }
//         }

//         updates
//     });
//     let applier = Box::new(move |updates: Vec<(Id, SatStatus)>, eg: &mut CHCEGraph| {
//         for (eclassId, satStatus) in updates {
//             assert!(eg.analysis_data(eclassId).satStatus == SatStatus::Unknown);
//             eg.analysis_data_mut(eclassId).satStatus = satStatus;
//         }
//     });
//     RewriteT {
//         name: "constraintRewrite".to_owned(),
//         searcher: searcher,
//         applier: applier,
//     }
//     .into()
// }
