use super::*;
use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Index,
};

use regex::Regex;

#[derive(Clone, Debug)]
pub enum ConstrOP {
    Eq,
    Neq,
    Add,
    Minus,
    Leq,
    Geq,
    Lt,
    Gt,
    EmptyList,
    List,
    Binode,
}

impl ConstrOP {
    fn name(&self) -> &str {
        match self {
            ConstrOP::Eq => "=",
            ConstrOP::Neq => "=\\=",
            ConstrOP::Add => "+",
            ConstrOP::Minus => "-",
            ConstrOP::Leq => "=<",
            ConstrOP::Geq => ">=",
            ConstrOP::Lt => "<",
            ConstrOP::Gt => ">",
            ConstrOP::EmptyList => "[]",
            ConstrOP::List => "list",
            ConstrOP::Binode => "node",
        }
    }

    fn toSExpr(&self) -> String {
        let s = format!("{:?}", self);
        let first = s.chars().next().unwrap().to_lowercase().collect::<String>();
        first + &s[1..]
    }

    fn childrenSameType(&self) -> bool {
        match self {
            ConstrOP::Eq | ConstrOP::Neq => true,
            ConstrOP::Add | ConstrOP::Minus => true,
            ConstrOP::Leq | ConstrOP::Geq | ConstrOP::Lt | ConstrOP::Gt => true,
            ConstrOP::EmptyList | ConstrOP::List | ConstrOP::Binode => false,
        }
    }

    fn childrenMustBeType(&self) -> Option<ArgType> {
        match self {
            ConstrOP::Eq | ConstrOP::Neq => None,
            ConstrOP::Add | ConstrOP::Minus => Some(ArgType::Int),
            ConstrOP::Leq | ConstrOP::Geq | ConstrOP::Lt | ConstrOP::Gt => Some(ArgType::Int),
            ConstrOP::EmptyList | ConstrOP::List | ConstrOP::Binode => None,
        }
    }

    fn getType(&self) -> ArgType {
        match self {
            ConstrOP::Eq | ConstrOP::Neq => ArgType::Bool,
            ConstrOP::Add | ConstrOP::Minus => ArgType::Int,
            ConstrOP::Leq | ConstrOP::Geq | ConstrOP::Lt | ConstrOP::Gt => ArgType::Bool,
            ConstrOP::EmptyList | ConstrOP::List => ArgType::List(Box::new(ArgType::Unknown)),
            ConstrOP::Binode => ArgType::Node(Box::new(ArgType::Unknown)),
        }
    }
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum CHCVar {
    Str(String),
    Int(i32),
}

impl CHCVar {
    pub fn toSExpr(&self, typeMap: &BTreeMap<CHCVar, ArgType>) -> String {
        match self {
            CHCVar::Str(s) => match typeMap.get(self).unwrap() {
                ArgType::Int => format!("(intType ${s})"),
                ArgType::Node(_) => format!("(nodeType ${s})"),
                ArgType::List(_) => format!("(listType ${s})"),
                _ => panic!("Unknown type {:?}", typeMap.get(self).unwrap()),
            },
            CHCVar::Int(i) => i.to_string(),
        }
    }

    pub fn toSlot(&self) -> Slot {
        match self {
            CHCVar::Str(s) => Slot::named(s),
            CHCVar::Int(i) => panic!(),
        }
    }
}

impl std::fmt::Debug for CHCVar {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self {
            CHCVar::Str(s) => write!(f, "{}", s),
            CHCVar::Int(i) => write!(f, "{}", i),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Constr {
    pub op: ConstrOP,
    pub args: Vec<Term>,
}

impl std::fmt::Display for Constr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}(", self.op.name())?;
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            match arg {
                Term::Var(v) => write!(f, "{:?}", v)?,
                Term::Constr(c) => write!(f, "{}", c)?,
            }
        }
        write!(f, ")")
    }
}

fn canUnionTypes(types: &BTreeSet<ArgType>) -> Option<ArgType> {
    let mut res = Some(ArgType::Unknown);
    for t in types {
        res = res.unwrap().union(&t);
        if res.is_none() {
            return None;
        }
    }

    res
}

impl Constr {
    pub fn toSExpr(&self, typeMap: &BTreeMap<CHCVar, ArgType>) -> String {
        format!(
            "({} {})",
            self.op.toSExpr(),
            self.args
                .iter()
                .map(|a| a.toSExpr(typeMap))
                .collect::<Vec<_>>()
                .join(" ")
        )
    }

    pub fn propagateTypeUp(&self, typeMap: &mut BTreeMap<CHCVar, ArgType>) -> ArgType {
        let mut types = Vec::new();
        for a in self.args.iter() {
            match a {
                Term::Var(v) => {
                    // children might not have type specified yet, if its type must be inferred from another constraint
                    // so we have to run this propagateType many times
                    if let Some(t) = typeMap.get(v) {
                        types.push(t.clone());
                    } else {
                        types.push(ArgType::Unknown);
                    }
                }
                Term::Constr(c) => {
                    let t = c.propagateTypeUp(typeMap);
                    types.push(t);
                }
            }
        }

        let allTypes: BTreeSet<ArgType> = types.iter().cloned().collect();
        if self.op.childrenSameType() {
            let mut inferType = canUnionTypes(&allTypes);
            assert!(
                inferType.is_some(),
                "not all Types are the same: {:?} {:?}",
                self,
                allTypes
            );
            let mustBeType = self.op.childrenMustBeType();
            if mustBeType.is_some() {
                inferType = inferType.unwrap().union(&mustBeType.unwrap());
            }
            assert!(inferType.is_some());

            if inferType == Some(ArgType::Unknown) {
                return ArgType::Bool;
            }

            let inferType = inferType.unwrap();
            for (i, t) in types.iter().enumerate() {
                // before, we already check that all types are the same
                if t == &inferType {
                    continue;
                }

                self.args[i].propagateTypeDown(inferType.clone(), typeMap);
            }

            return self.op.getType();
        }

        match self.op {
            ConstrOP::EmptyList => self.op.getType(),
            ConstrOP::List => {
                assert!(self.args.len() == 2);

                let mut allTypes: BTreeSet<ArgType> = BTreeSet::new();
                let headType = types[0].clone();
                if headType != ArgType::Unknown {
                    allTypes.insert(headType.clone());
                }
                let tailType = types[1].clone();
                match &tailType {
                    ArgType::List(t) => {
                        if t.as_ref() != &ArgType::Unknown {
                            allTypes.insert(t.as_ref().clone());
                        }
                    }
                    _ => {}
                }
                assert!(allTypes.len() <= 1);

                let inferType = if allTypes.len() == 1 {
                    Some(allTypes.iter().next().unwrap().clone())
                } else {
                    None
                };

                if inferType.is_none() {
                    return self.op.getType();
                }

                let inferType = inferType.unwrap();
                if headType == ArgType::Unknown {
                    self.args[0].propagateTypeDown(inferType.clone(), typeMap);
                }

                if tailType == ArgType::Unknown
                    || tailType == ArgType::List(Box::new(ArgType::Unknown))
                {
                    self.args[1]
                        .propagateTypeDown(ArgType::List(Box::new(inferType.clone())), typeMap);
                }

                ArgType::List(Box::new(inferType.clone()))
            }
            ConstrOP::Binode => {
                assert!(self.args.len() == 3);
                let elType = types[0].clone();
                let leftType = types[1].clone();
                let rightType = types[2].clone();

                let mut allTypes = BTreeSet::new();
                if elType != ArgType::Unknown {
                    allTypes.insert(elType.clone());
                }
                match &leftType {
                    ArgType::Node(t) => {
                        if t.as_ref() != &ArgType::Unknown {
                            allTypes.insert(t.as_ref().clone());
                        }
                    }
                    _ => {}
                }
                match &rightType {
                    ArgType::Node(t) => {
                        if t.as_ref() != &ArgType::Unknown {
                            allTypes.insert(t.as_ref().clone());
                        }
                    }
                    _ => {}
                }

                assert!(allTypes.len() <= 1);

                let inferType = if allTypes.len() == 1 {
                    Some(allTypes.iter().next().unwrap().clone())
                } else {
                    None
                };

                if inferType.is_none() {
                    return self.op.getType();
                }

                let inferType = inferType.unwrap();
                if elType == ArgType::Unknown {
                    self.args[0].propagateTypeDown(inferType.clone(), typeMap);
                }
                if leftType == ArgType::Unknown {
                    self.args[1]
                        .propagateTypeDown(ArgType::Node(Box::new(inferType.clone())), typeMap);
                }
                if rightType == ArgType::Unknown {
                    self.args[2]
                        .propagateTypeDown(ArgType::Node(Box::new(inferType.clone())), typeMap);
                }

                ArgType::Node(Box::new(inferType.clone()))
            }
            _ => panic!("Shouldn't reach here"),
        }
    }

    pub fn propagateTypeDown(&self, thisType: ArgType, typeMap: &mut BTreeMap<CHCVar, ArgType>) {
        match self.op {
            ConstrOP::Eq | ConstrOP::Neq | ConstrOP::EmptyList => {}
            ConstrOP::Add
            | ConstrOP::Minus
            | ConstrOP::Leq
            | ConstrOP::Geq
            | ConstrOP::Lt
            | ConstrOP::Gt => {
                for a in self.args.iter() {
                    a.propagateTypeDown(ArgType::Int, typeMap);
                }
            }
            ConstrOP::Binode => {
                assert!(self.args.len() == 3);
                let ArgType::Node(elType) = thisType else {
                    panic!("should be type node");
                };
                let elType = elType.as_ref();
                assert!(elType != &ArgType::Unknown);

                self.args[0].propagateTypeDown(elType.clone(), typeMap);
                self.args[1].propagateTypeDown(ArgType::Node(Box::new(elType.clone())), typeMap);
                self.args[2].propagateTypeDown(ArgType::Node(Box::new(elType.clone())), typeMap);
            }
            ConstrOP::List => {
                assert!(self.args.len() == 2);
                let ArgType::List(elType) = thisType else {
                    panic!("should be type list {:?}", thisType);
                };
                let elType = elType.as_ref();
                assert!(elType != &ArgType::Unknown);

                self.args[0].propagateTypeDown(elType.clone(), typeMap);
                self.args[1].propagateTypeDown(ArgType::List(Box::new(elType.clone())), typeMap);
            }
        }
    }
}

#[derive(Clone)]
pub enum Term {
    Var(CHCVar),
    Constr(Constr),
}

impl std::fmt::Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Term::Var(v) => write!(f, "{:?}", v),
            Term::Constr(c) => write!(f, "{:?}", c),
        }
    }
}

impl Term {
    pub fn isVar(&self) -> bool {
        match self {
            Term::Var(_) => true,
            _ => false,
        }
    }

    pub fn getVar(&self) -> Option<&CHCVar> {
        match self {
            Term::Var(v) => Some(v),
            _ => None,
        }
    }

    pub fn toSExpr(&self, typeMap: &BTreeMap<CHCVar, ArgType>) -> String {
        match self {
            Term::Var(v) => v.toSExpr(typeMap),
            Term::Constr(c) => c.toSExpr(typeMap),
        }
    }

    pub fn propagateTypeDown(&self, thisType: ArgType, typeMap: &mut BTreeMap<CHCVar, ArgType>) {
        match self {
            Term::Var(v) => {
                let mut updateToType = Some(thisType);
                if let Some(t) = typeMap.get(v) {
                    updateToType = t.union(&updateToType.unwrap());
                    assert!(updateToType.is_some());
                }
                typeMap.insert(v.clone(), updateToType.unwrap());
            }
            Term::Constr(c) => {
                c.propagateTypeDown(thisType, typeMap);
            }
        }
    }
}

#[derive(Clone)]
pub struct Args {
    pub args: Vec<Term>,
}

impl std::fmt::Debug for Args {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self.args)
    }
}

impl Args {
    pub fn new(args: Vec<Term>) -> Args {
        Args { args }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, Term> {
        self.args.iter()
    }

    pub fn isAllVar(&self) -> bool {
        self.args.iter().all(|a| a.isVar())
    }
}

impl Into<Args> for Vec<Term> {
    fn into(self) -> Args {
        Args { args: self }
    }
}

impl Index<usize> for Args {
    type Output = Term;

    fn index(&self, index: usize) -> &Self::Output {
        &self.args[index]
    }
}

#[derive(Clone, Debug)]
pub struct PredApp {
    pub pred_name: String,
    pub args: Args,
}

impl std::fmt::Display for PredApp {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}(", self.pred_name)?;
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", arg)?;
        }
        write!(f, ")")
    }
}

impl PredApp {
    pub fn renameAll(&mut self, count: &mut usize) -> Vec<Constr> {
        let mut newConstr = Vec::new();
        let mut new_args: Vec<Term> = self
            .args
            .iter()
            .map(|a| {
                newConstr.push(Constr {
                    op: ConstrOP::Eq,
                    args: vec![a.clone(), Term::Var(CHCVar::Str(format!("new{}", count)))],
                });
                let ret = Term::Var(CHCVar::Str(format!("new{}", count)));
                *count += 1;
                ret
            })
            .collect();

        self.args = new_args.into();
        newConstr
    }

    pub fn renameTerm(&mut self, count: &mut usize) -> Vec<Constr> {
        let mut newConstr = Vec::new();
        let mut new_args: Vec<Term> = self
            .args
            .iter()
            .map(|a| {
                if a.isVar() {
                    a.clone()
                } else {
                    newConstr.push(Constr {
                        op: ConstrOP::Eq,
                        args: vec![a.clone(), Term::Var(CHCVar::Str(format!("new{}", count)))],
                    });
                    let ret = Term::Var(CHCVar::Str(format!("new{}", count)));
                    *count += 1;
                    ret
                }
            })
            .collect();

        self.args = new_args.into();
        newConstr
    }

    pub fn toHeadSExpr(&self, typeMap: &BTreeMap<CHCVar, ArgType>) -> String {
        assert!(self.args.isAllVar());

        format!(
            "(pred <{}>)",
            self.args
                .iter()
                .map(|a| a.toSExpr(typeMap))
                .collect::<Vec<_>>()
                .join(" ")
        )
    }

    pub fn toTailSExpr(&self, props: &PredProp, typeMap: &BTreeMap<CHCVar, ArgType>) -> String {
        let predName = self.pred_name.clone();
        let syntax = self.toHeadSExpr(typeMap);
        format!(
            "(composeInit {predName} {syntax} ({}) <{}>)",
            props.functional,
            props
                .outputIdx
                .iter()
                .map(|i| format!("{}", i))
                .collect::<Vec<_>>()
                .join(" ")
        )
    }

    pub fn retrieveTypes(&self, typeMap: &mut BTreeMap<CHCVar, ArgType>, props: &PredProp) {
        let types = &props.types;
        for (i, t) in types.iter().enumerate() {
            typeMap.insert(self.args[i].clone().getVar().unwrap().clone(), t.clone());
        }
    }
}

#[derive(Clone, Debug)]
pub struct CHCRule {
    pub head: PredApp,
    pub constr: Vec<Constr>,
    pub pred_apps: Vec<PredApp>,
    pub original: String,
}

#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Ord)]
pub enum ArgType {
    Int,
    Node(Box<ArgType>),
    Unknown,
    Bool,
    List(Box<ArgType>),
}

impl ArgType {
    pub fn union(&self, other: &ArgType) -> Option<ArgType> {
        if self == other {
            return Some(self.clone());
        }

        if self == &ArgType::Unknown {
            return Some(other.clone());
        }

        if other == &ArgType::Unknown {
            return Some(self.clone());
        }

        assert!(self != &ArgType::Unknown && other != &ArgType::Unknown);
        match (self, other) {
            (ArgType::Node(t1), ArgType::Node(t2)) => {
                let res = t1.union(t2);
                if res.is_none() {
                    return None;
                }
                Some(ArgType::Node(Box::new(res.unwrap())))
            }
            (ArgType::List(t1), ArgType::List(t2)) => {
                let res = t1.union(t2);
                if res.is_none() {
                    return None;
                }
                Some(ArgType::List(Box::new(res.unwrap())))
            }
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct PredProp {
    pub types: Vec<ArgType>,
    pub functional: bool,
    pub outputIdx: Vec<usize>,
}

#[derive(Clone, Debug)]
pub struct CHCAst {
    pub rules: Vec<CHCRule>,
    pub preds: BTreeMap<String, PredProp>,
}

impl CHCRule {
    // TODO: turn prop into typeMap: var -> type first
    pub fn noTermInPredApp(&self) -> bool {
        self.pred_apps.iter().all(|p| p.args.isAllVar()) && self.head.args.isAllVar()
    }

    pub fn toSExpr(
        &self,
        prop: &BTreeMap<String, PredProp>,
        typeMap: &BTreeMap<CHCVar, ArgType>,
    ) -> String {
        let mut varToType = BTreeMap::new();
        for (i, v) in self.head.args.iter().enumerate() {
            let v = v.getVar().unwrap();
            varToType.insert(
                v.clone(),
                prop.get(&self.head.pred_name).unwrap().types[i].clone(),
            );
        }
        format!(
            "(new {} {} {})",
            self.head.toHeadSExpr(typeMap),
            format!(
                "(and <{}>)",
                self.constr
                    .iter()
                    .map(|c| c.toSExpr(typeMap))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            format!(
                "<{}>",
                self.pred_apps
                    .iter()
                    .map(|p| p.toTailSExpr(prop.get(&p.pred_name).unwrap(), typeMap))
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        )
    }

    pub fn getTypeInfo(&self, prop: &BTreeMap<String, PredProp>) -> BTreeMap<CHCVar, ArgType> {
        assert!(self.noTermInPredApp());
        let mut typeMap = BTreeMap::new();

        for (i, v) in self.head.args.iter().enumerate() {
            let v = v.getVar().unwrap();
            typeMap.insert(
                v.clone(),
                prop.get(&self.head.pred_name).unwrap().types[i].clone(),
            );
        }

        for p in self.pred_apps.iter() {
            for (i, v) in p.args.iter().enumerate() {
                let v = v.getVar().unwrap();
                typeMap.insert(v.clone(), prop.get(&p.pred_name).unwrap().types[i].clone());
            }
        }

        typeMap
    }
}

impl std::fmt::Display for CHCRule {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "CHC({}, [", self.head)?;
        for (i, c) in self.constr.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", c)?;
        }
        write!(f, "], [")?;
        for (i, p) in self.pred_apps.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", p)?;
        }
        write!(f, "])")
    }
}
