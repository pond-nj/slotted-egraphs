use std::collections::{BTreeMap, BTreeSet};

use regex::Regex;

#[derive(Clone, Debug)]
pub enum ConstrOP {
    Eq,
    Neq,
    Add,
    Minus,
    Leq,
    Geq,
    Less,
    Greater,
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
            ConstrOP::Less => "<",
            ConstrOP::Greater => ">",
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
}

#[derive(Clone)]
pub enum CHCVar {
    Str(String),
    Int(i32),
}

impl CHCVar {
    pub fn toSExpr(&self) -> String {
        match self {
            CHCVar::Str(s) => format!("${s}"),
            CHCVar::Int(i) => i.to_string(),
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

impl Constr {
    pub fn toSExpr(&self) -> String {
        format!(
            "({} {})",
            self.op.toSExpr(),
            self.args
                .iter()
                .map(|a| a.toSExpr())
                .collect::<Vec<_>>()
                .join(" ")
        )
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

    pub fn toSExpr(&self) -> String {
        match self {
            Term::Var(v) => v.toSExpr(),
            Term::Constr(c) => c.toSExpr(),
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

    pub fn iter(&self) -> std::slice::Iter<Term> {
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

    pub fn toHeadSExpr(&self) -> String {
        assert!(self.args.isAllVar());

        format!(
            "(pred <{}>)",
            self.args
                .iter()
                .map(|a| a.toSExpr())
                .collect::<Vec<_>>()
                .join(" ")
        )
    }

    pub fn toTailSExpr(&self, props: &BTreeMap<String, PredProp>) -> String {
        let predName = self.pred_name.clone();
        let syntax = self.toHeadSExpr();
        format!(
            "(composeInit {predName} {syntax} ({}) <{}>)",
            props.get(&predName).unwrap().functional,
            props
                .get(&predName)
                .unwrap()
                .outputIdx
                .iter()
                .map(|i| format!("{}", i))
                .collect::<Vec<_>>()
                .join(" ")
        )
    }
}

#[derive(Clone, Debug)]
pub struct CHCRule {
    pub head: PredApp,
    pub constr: Vec<Constr>,
    pub pred_apps: Vec<PredApp>,
    pub original: String,
}

#[derive(Clone, Debug)]
pub enum ArgType {
    Int,
    Node,
    Unknown,
    List,
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
    pub fn rename_head(&mut self) {
        let mut count = 0;
        let mut new_args = Vec::new();
        for _ in self.head.args.iter() {
            count += 1;
            new_args.push(Term::Var(CHCVar::Str(format!("new{}", count - 1))));
        }
        let new_head = PredApp {
            pred_name: self.head.pred_name.clone(),
            args: Args::new(new_args),
        };

        for (i, v) in self.head.args.iter().enumerate() {
            self.constr.push(Constr {
                op: ConstrOP::Eq,
                args: vec![v.clone(), Term::Var(CHCVar::Str(format!("new{}", i)))],
            });
        }

        self.head = new_head;
    }

    pub fn toSExpr(&self, prop: &BTreeMap<String, PredProp>) -> String {
        format!(
            "(new {} {} {})",
            self.head.toHeadSExpr(),
            format!(
                "(and <{}>)",
                self.constr
                    .iter()
                    .map(|c| c.toSExpr())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            format!(
                "<{}>",
                self.pred_apps
                    .iter()
                    .map(|p| p.toTailSExpr(prop))
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        )
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
