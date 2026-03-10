use std::{fs::File, path::Path};

use super::*;

pub fn toSMTType(varType: &VarType) -> String {
    match varType {
        VarType::Unknown => "unknown".to_string(),
        VarType::Int => "Int".to_string(),
        VarType::Node => "tree".to_string(),
        VarType::List => "list".to_string(),
    }
}

// This will appear in an enclosed parenthesis
fn enodeToSMTOp(enode: &CHC) -> &'static str {
    match enode {
        CHC::Add(..) => "+",
        CHC::And(..) => "and",
        CHC::Eq(..) => "=",
        CHC::Greater(..) => ">",
        CHC::Geq(..) => ">=",
        CHC::Less(..) => "<",
        CHC::Leq(..) => "<=",
        CHC::BiNode(..) => "binode",
        CHC::Minus(..) => "-",

        _ => todo!(),
    }
}

fn patternToSMTLib(pattern: &Pattern<CHC>) -> String {
    let mut out = String::new();
    let Pattern::ENode(node, children) = pattern else {
        panic!()
    };

    let ret = match node {
        CHC::IntType(s) => Some(s.to_string()),
        CHC::NodeType(s) => Some(s.to_string()),
        CHC::ListType(s) => Some(s.to_string()),
        CHC::Leaf() => Some("leaf".to_string()),
        CHC::Number(n) => Some(format!("{}", n)),
        CHC::True() => Some("true".to_string()),
        _ => None,
    };

    if ret.is_some() {
        return ret.unwrap();
    }

    let op = enodeToSMTOp(node);
    let childrenExpr = children
        .iter()
        .map(|child| patternToSMTLib(child))
        .collect::<Vec<_>>()
        .join(" ");

    "(".to_string() + &op + " " + &childrenExpr + ")"
}

pub fn synSMTLibExpr(eclassId: Id, eg: &CHCEGraph) -> String {
    // TODO: get type info first
    let mut map = BTreeMap::default();
    let mut calls = BTreeMap::default();
    let expr = eg.getSynExpr(&eclassId, &mut map, &mut calls);

    if expr.is_err() {
        return expr.unwrap_err();
    }

    let mut out = String::new();
    out += &("; ".to_string() + &expr.as_ref().unwrap().to_string() + "\n");

    let pattern = re_to_pattern(expr.unwrap());

    let mut types = BTreeMap::default();
    aggregateType(&pattern, &mut types);

    out += "(set-option :produce-models true)\n";
    out += "(declare-datatypes ((tree 0)) (((binode  (data Int) (left tree) (right tree)) (leaf ))))\n";
    for (s, vt) in types {
        out += &format!("(declare-const {s} {})\n", toSMTType(&vt));
    }
    out += "\n";
    out += &format!("(assert {})", &patternToSMTLib(&pattern));
    out += "\n";
    out += "(check-sat)\n";
    // out += "(get-model)\n";

    out
}

pub fn dumpAndExprSMT(dirName: &str, eg: &CHCEGraph) {
    if Path::new(dirName).exists() {
        let oldDirName = dirName.to_string() + ".old";
        if Path::new(&oldDirName).exists() {
            std::fs::remove_dir_all(&oldDirName).unwrap();
        }
        std::fs::rename(dirName, oldDirName).unwrap();
    }

    std::fs::create_dir(dirName).unwrap();

    let ids = eg.ids();
    for eclassId in ids {
        let mut doPrint = false;
        for enode in eg.enodes(eclassId) {
            match enode {
                CHC::And(..) => {
                    doPrint = true;
                    break;
                }
                _ => {}
            }
        }

        if !doPrint {
            continue;
        }

        // create a file name eclassId in dirName
        let fileName = format!("{dirName}/{eclassId:?}.smt2");
        // write to file
        let mut file = File::create(fileName).unwrap();
        file.write_all(synSMTLibExpr(eclassId, eg).as_bytes())
            .unwrap();
    }
}
