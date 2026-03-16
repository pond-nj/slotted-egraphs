use super::*;

use kmpsearch::Haystack;
use regex::Regex;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use std::str::{CharIndices, Chars};

fn group_lines(lines: Vec<String>) -> Vec<String> {
    let mut new_lines = Vec::new();
    let mut curr_line = String::new();
    for line in lines {
        let line = line.replace("\n", "");
        for c in line.chars() {
            if c == '.' {
                new_lines.push(format!("{}{}", curr_line, c));
                curr_line.clear();
            } else {
                curr_line.push(c);
            }
        }
    }
    if !curr_line.is_empty() {
        new_lines.push(curr_line);
    }
    new_lines
}

fn parse_body(expression: &str) -> Vec<String> {
    let mut result = Vec::new();
    let mut current = String::new();
    let mut bracket_count = 0;

    for char in expression.chars() {
        if char == '(' {
            bracket_count += 1;
            current.push(char);
        } else if char == ')' {
            bracket_count -= 1;
            current.push(char);
        } else if char == ',' && bracket_count == 0 {
            result.push(current.trim().to_string());
            current.clear();
        } else {
            current.push(char);
        }
    }

    if !current.trim().is_empty() {
        result.push(current.trim().to_string());
    }

    result
}

fn find_subslice_kmp(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack.first_indexof_needle(needle)
}

// counting at at_pos
fn get_level(at_pos: usize, from_pos: usize, from_level: usize, expr: &str) -> usize {
    assert!(at_pos >= from_pos);
    assert!(at_pos < expr.len());

    let mut level = from_level;
    let mut currPos = from_pos;

    while currPos <= at_pos {
        let c = &expr[currPos..currPos + 1].chars().next().unwrap();

        if *c == '(' {
            level += 1;
        } else if *c == ')' {
            level -= 1;
        }

        currPos += 1;
    }

    level
}

// find the first occurence at level 0 of this operator
fn split_at_level_0(expr: &str, op: ConstrOP) -> Option<(String, String)> {
    let opChars = op.name();

    let mut currPos = 0;
    let mut currLevel = 0;
    let mut nextPos = expr.find(&opChars);
    while nextPos.is_some() {
        let mut level = get_level(nextPos.unwrap(), currPos, currLevel, expr);
        if level == 0 {
            return Some((
                expr[0..nextPos.unwrap()].trim().to_string(),
                expr[opChars.len() + nextPos.unwrap()..].trim().to_string(),
            ));
        }
        currLevel = level;
        currPos = nextPos.unwrap();
        nextPos = expr[currPos + 1..].find(&opChars);
    }

    None
}

fn split_constr(expr: &str) -> Option<(ConstrOP, String, String)> {
    if let Some((first, rest)) = split_at_level_0(expr, ConstrOP::Neq) {
        return Some((ConstrOP::Neq, first, rest));
    } else if let Some((first, rest)) = split_at_level_0(expr, ConstrOP::Leq) {
        return Some((ConstrOP::Leq, first, rest));
    } else if let Some((first, rest)) = split_at_level_0(expr, ConstrOP::Geq) {
        return Some((ConstrOP::Geq, first, rest));
    } else if let Some((first, rest)) = split_at_level_0(expr, ConstrOP::Lt) {
        return Some((ConstrOP::Lt, first, rest));
    } else if let Some((first, rest)) = split_at_level_0(expr, ConstrOP::Gt) {
        return Some((ConstrOP::Gt, first, rest));
    } else if let Some((first, rest)) = split_at_level_0(expr, ConstrOP::Eq) {
        return Some((ConstrOP::Eq, first, rest));
    }

    None
}

fn split_args(args: &str) -> Vec<String> {
    // only split on commas that are not inside parentheses
    let mut result = vec![];
    let mut current = String::new();
    let mut bracket_count = 0;

    for char in args.chars() {
        if char == '(' {
            bracket_count += 1;
            current.push(char);
        } else if char == ')' {
            bracket_count -= 1;
            current.push(char);
        } else if char == ',' && bracket_count == 0 {
            result.push(current.trim().to_string());
            current.clear();
        } else {
            current.push(char);
        }
    }

    if !current.trim().is_empty() {
        result.push(current.trim().to_string());
    }

    result
}

fn parse_prolog(lines: &Vec<String>) -> Vec<CHCRule> {
    let mut chcs = Vec::new();
    let head_re = Regex::new(r"^(\w*)\((.*)\)$").unwrap();

    for line in lines {
        let mut line = line.trim().to_string();
        if line.starts_with("%") {
            continue;
        }
        if line.starts_with("#t") {
            continue;
        }
        if line.is_empty() {
            continue;
        }

        if line.ends_with('.') {
            line = line[..line.len() - 1].to_string();
        }

        let (head, body) = if line.contains(":-") {
            let parts: Vec<&str> = line.split(":-").collect();
            (parts[0].trim().to_string(), parts[1].trim().to_string())
        } else {
            if !head_re.is_match(&line) {
                panic!("Invalid head format: {}", line);
            }
            (line.clone(), String::new())
        };

        let head_pred = if head.contains('(') {
            head.split('(').next().unwrap().to_string()
        } else {
            head.clone()
        };

        let head_args: Vec<Term> = if head.contains('(') {
            assert!(head_re.is_match(&head), "Invalid head format: {}", head);

            let caps = head_re.captures(&head).unwrap();
            let args_str = caps.get(2).unwrap().as_str();

            split_args(args_str)
                .iter()
                .map(|x: &String| {
                    parse_constr(x.trim())
                        .expect(format!("parse_constr returned None on {x} in {head}").as_str())
                })
                .collect()
        } else {
            Vec::new()
        };

        let mut constrs = Vec::new();
        let mut pred_apps = Vec::new();

        let body_parts = parse_body(&body);

        let pred_re = Regex::new(r"^(\w*)\((.*)\)$").unwrap();
        let node_re = Regex::new(r"^node\((.*)\)$").unwrap();

        for b in body_parts {
            let b = b.trim().to_string();
            if pred_re.is_match(&b) {
                let caps = pred_re.captures(&b).unwrap();
                let b_pred = caps.get(1).unwrap().as_str().to_string();
                let b_args_str = caps.get(2).unwrap().as_str();
                let b_args = b_args_str
                    .split(',')
                    .map(|x| parse_constr(x.trim()).unwrap())
                    .collect();
                pred_apps.push(PredApp {
                    pred_name: b_pred,
                    args: Args::new(b_args),
                });
            } else {
                // Handle node specially if needed, but parse_constr handles it
                if let Some(parsed) = parse_constr(&b) {
                    if let Term::Constr(c) = parsed {
                        constrs.push(c);
                    }
                }
            }
        }

        let res = CHCRule {
            head: PredApp {
                pred_name: head_pred,
                args: Args::new(head_args),
            },
            constr: constrs,
            pred_apps,
            original: line,
        };
        chcs.push(res);
    }
    chcs
}

pub fn parse(fname: &str) -> CHCAst {
    let path = Path::new(fname);
    let file = File::open(&path).expect("Failed to open file");
    let lines: Vec<String> = io::BufReader::new(file)
        .lines()
        .map(|l| l.unwrap())
        .collect();

    let new_lines = group_lines(lines);
    let rules = parse_prolog(&new_lines);

    let props = parse_properties(&new_lines);

    let pred_from_rules: BTreeSet<String> =
        rules.iter().map(|r| r.head.pred_name.clone()).collect();
    let pred_from_props: BTreeSet<String> = props.keys().cloned().collect();
    assert_eq!(
        pred_from_rules, pred_from_props,
        "predicate properties not all specified"
    );

    CHCAst {
        rules,
        preds: props,
    }
}

fn parse_properties(lines: &Vec<String>) -> BTreeMap<String, PredProp> {
    let mut props = BTreeMap::new();

    for line in lines {
        let line = &line.trim().to_string();
        if !line.starts_with("#t") {
            continue;
        }

        let re = Regex::new(r"^#t\s*(\w*)\((.*)\) (true|false) <(.*)>.$").unwrap();
        let caps: regex::Captures<'_> = re
            .captures(&line)
            .expect("Line does not match expected format");

        let pred_name = caps.get(1).unwrap().as_str().to_string();

        let mut types = Vec::<ArgType>::new();

        let arg_type_str = caps.get(2).unwrap().as_str();
        let arg_types: Vec<String> = arg_type_str
            .split(',')
            .map(|s| s.trim().to_string())
            .collect();
        for t in &arg_types {
            if t == "" {
                continue;
            }

            match t.as_str() {
                "int" => types.push(ArgType::Int),
                "node" => types.push(ArgType::Node(Box::new(ArgType::Unknown))),
                "node(int)" => types.push(ArgType::Node(Box::new(ArgType::Int))),
                "list" => types.push(ArgType::List(Box::new(ArgType::Unknown))),
                "list(int)" => types.push(ArgType::List(Box::new(ArgType::Int))),
                _ => panic!("Unknown arg type {}", t),
            }
        }

        let is_true = caps.get(3).unwrap().as_str() == "true";
        let idx: Vec<String> = caps
            .get(4)
            .unwrap()
            .as_str()
            .split_whitespace()
            .map(|s| s.to_string())
            .collect();

        props.insert(
            pred_name.clone(),
            PredProp {
                types,
                functional: is_true,
                outputIdx: idx.iter().map(|s| s.parse::<usize>().unwrap()).collect(),
            },
        );
    }

    props
}

fn parse_constr(constr: &str) -> Option<Term> {
    // let orig_constr = constr.to_string();
    let mut constr = constr.trim().to_string();

    if constr.parse::<i32>().is_ok() {
        return Some(Term::Var(CHCVar::Int(constr.parse::<i32>().unwrap())));
    }

    if constr == "leaf" {
        return Some(Term::Constr(Constr {
            op: ConstrOP::Leaf,
            args: Vec::new(),
        }));
    }

    if Regex::new(r"^\w+$").unwrap().is_match(&constr) {
        return Some(Term::Var(CHCVar::Str(constr)));
    }

    if constr == "[]" {
        return Some(Term::Constr(Constr {
            op: ConstrOP::EmptyList,
            args: Vec::new(),
        }));
    }

    if constr.starts_with('[') && constr.ends_with(']') {
        constr = constr[1..constr.len() - 1].to_string();
        if constr.contains('|') {
            let parts: Vec<&str> = constr.split('|').collect();
            if parts.len() != 2 {
                return None;
            }
            let left = parse_constr(parts[0].trim())?;
            let right = parse_constr(parts[1].trim())?;
            return Some(Term::Constr(Constr {
                op: ConstrOP::List,
                args: vec![left, right],
            }));
        } else {
            if !Regex::new(r"^\w+$").unwrap().is_match(&constr) {
                return None;
            }
            let left = parse_constr(&constr)?;
            let right = Term::Constr(Constr {
                op: ConstrOP::EmptyList,
                args: Vec::new(),
            });
            return Some(Term::Constr(Constr {
                op: ConstrOP::List,
                args: vec![left, right],
            }));
        }
    }

    let node_re = Regex::new(r"^node\((.*)\)$").unwrap();
    if let Some(caps) = node_re.captures(&constr) {
        let args_str = caps.get(1).unwrap().as_str();
        let args: Vec<&str> = args_str.split(',').collect();
        if args.len() != 3 {
            return None;
        }
        let arg0 = parse_constr(args[0].trim())?;
        let arg1 = parse_constr(args[1].trim())?;
        let arg2 = parse_constr(args[2].trim())?;
        return Some(Term::Constr(Constr {
            op: ConstrOP::Binode,
            args: vec![arg0, arg1, arg2],
        }));
    }

    // split constr into first term and rest using =, =\\=, =<, >=, <, >

    if let Some((op, first, second)) = split_constr(&constr) {
        let child1 = parse_constr(&first)?;
        let child2 = parse_constr(&second)?;
        return Some(Term::Constr(Constr {
            op,
            args: vec![child1, child2],
        }));
    }

    let (first, rest) = constr_get_next_term(&constr);
    let (op_str, next_constr) = constr_get_next_term(&rest);

    let op = match op_str.as_str() {
        "+" => ConstrOP::Add,
        "-" => ConstrOP::Minus,
        _ => return None,
    };
    let child1 = parse_constr(&first)?;
    let child2 = parse_constr(&next_constr)?;
    Some(Term::Constr(Constr {
        op,
        args: vec![child1, child2],
    }))
}

fn constr_get_next_term(constr: &str) -> (String, String) {
    let constr = constr.trim().chars().collect::<Vec<_>>();
    let mut i = 0;
    let mut bracket_count = 0;

    let mut first_is_var_not_op = false;
    if !constr.is_empty() {
        let first_char = constr[0];
        if first_char.is_alphabetic() || first_char.is_ascii_digit() {
            first_is_var_not_op = true;
        }
    }
    while i < constr.len() {
        let c = constr[i];
        if c == ' ' && bracket_count == 0 {
            break;
        }

        if first_is_var_not_op && !c.is_alphabetic() && !c.is_ascii_digit() && bracket_count == 0 {
            break;
        }

        if !first_is_var_not_op && (c.is_alphabetic() || c.is_ascii_digit()) && bracket_count == 0 {
            break;
        }

        if c == '(' || c == '[' {
            bracket_count += 1;
        } else if c == ')' || c == ']' {
            bracket_count -= 1;
        }

        i += 1;
    }
    (constr[..i].iter().collect(), constr[i..].iter().collect())
}
