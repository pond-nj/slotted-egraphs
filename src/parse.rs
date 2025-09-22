use crate::*;

#[derive(Debug, Clone)]
pub enum ParseError {
    TokenState(String),
    ParseState(Vec<Token>),
    RemainingRest(Vec<Token>),
    FromSyntaxFailed(Vec<SyntaxElem>),
    ExpectedColonEquals(Vec<Token>),
    ExpectedRBracket(Vec<Token>),
}

#[derive(Debug, Clone)]
pub enum Token {
    Slot(Slot),    // $42
    Ident(String), // map, 15
    PVar(String),  // ?x
    ColonEquals,   // :=
    LParen,        // (
    RParen,        // )
    LBracket,      // [
    RBracket,      // ]
    LVecBracket,   // <
    RVecBracket,   // >
}

fn ident_char(c: char) -> bool {
    if c.is_whitespace() {
        return false;
    }
    if "()[]<>".contains(c) {
        return false;
    }
    true
}

fn crop_ident(s: &str) -> Result<(/*ident*/ &str, /*rest*/ &str), ParseError> {
    let out = if let Some((i, _)) = s.char_indices().find(|(_, x)| !ident_char(*x)) {
        (&s[..i], &s[i..])
    } else {
        (s, "")
    };

    if out.0.is_empty() {
        return Err(ParseError::TokenState(s.to_string()));
    }

    Ok(out)
}

fn tokenize(mut s: &str) -> Result<Vec<Token>, ParseError> {
    let mut tokens = Vec::new();

    loop {
        s = s.trim_start();
        if s.is_empty() {
            break;
        }

        if s.starts_with('(') {
            tokens.push(Token::LParen);
            s = &s[1..];
        } else if s.starts_with(')') {
            tokens.push(Token::RParen);
            s = &s[1..];
        } else if s.starts_with('[') {
            tokens.push(Token::LBracket);
            s = &s[1..];
        } else if s.starts_with(']') {
            tokens.push(Token::RBracket);
            s = &s[1..];
        } else if s.starts_with("<") {
            tokens.push(Token::LVecBracket);
            s = &s[1..];
        } else if s.starts_with(">") {
            tokens.push(Token::RVecBracket);
            s = &s[1..];
        } else if s.starts_with(":=") {
            tokens.push(Token::ColonEquals);
            s = &s[2..];
        } else if s.starts_with('?') {
            let (op, rst) = crop_ident(&s[1..])?;
            tokens.push(Token::PVar(op.to_string()));
            s = rst;
        } else if s.starts_with('$') {
            let (op, rst) = crop_ident(&s[1..])?;
            tokens.push(Token::Slot(Slot::named(op)));
            s = rst;
        } else {
            let (op, rst) = crop_ident(s)?;
            tokens.push(Token::Ident(op.to_string()));
            s = rst;
        }
    }

    eprintln!("tokenize: ret = {:?}", tokens);
    Ok(tokens)
}

// parse:
impl<L: Language> Pattern<L> {
    pub fn parse(s: &str) -> Result<Self, ParseError> {
        println!("\ns = {:?}", s);
        let tok = tokenize(s)?;
        let (re, rest) = parse_pattern(&tok)?;

        if !rest.is_empty() {
            return Err(ParseError::RemainingRest(to_vec(rest)));
        }

        Ok(re)
    }
}

impl<L: Language> RecExpr<L> {
    pub fn parse(s: &str) -> Result<Self, ParseError> {
        let pat = Pattern::parse(s)?;
        let ret = pattern_to_re(&pat);
        eprintln!("RecExpr::parse: ret = {:?}", ret);
        Ok(ret)
    }
}

fn parse_pattern<L: Language>(tok: &[Token]) -> Result<(Pattern<L>, &[Token]), ParseError> {
    println!("parse_pattern input tok = {:?}", tok);
    let (mut pat, mut tok) = parse_pattern_nosubst(tok)?;
    // Case [:=]?
    while let Some(Token::LBracket) = tok.get(0) {
        tok = &tok[1..];
        let (l, tok2) = parse_pattern(tok)?;
        tok = tok2;

        let Token::ColonEquals = &tok[0] else {
            return Err(ParseError::ExpectedColonEquals(to_vec(tok)));
        };
        tok = &tok[1..];

        let (r, tok2) = parse_pattern(tok)?;
        tok = tok2;

        let Token::RBracket = &tok[0] else {
            return Err(ParseError::ExpectedRBracket(to_vec(tok)));
        };
        tok = &tok[1..];

        pat = Pattern::Subst(Box::new(pat), Box::new(l), Box::new(r));
    }
    let ret = (pat.clone(), tok);
    println!(
        "parse_pattern pat_struct = {:#?}, pat_display = {}",
        ret.0, pat
    );
    Ok(ret)
}

fn nested_syntax_elem_to_syntax_elem<L: Language>(ne: &NestedSyntaxElem<L>) -> SyntaxElem {
    match ne {
        NestedSyntaxElem::String(s) => SyntaxElem::String(s.clone()),
        NestedSyntaxElem::Slot(s) => SyntaxElem::Slot(*s),
        NestedSyntaxElem::Pattern(_) => SyntaxElem::AppliedId(AppliedId::null()),
        NestedSyntaxElem::Vec(v) => SyntaxElem::Vec(
            v.into_iter()
                .map(nested_syntax_elem_to_syntax_elem)
                .collect(),
        ),
    }
}

// no substitutions. = dont deal with [:=]
fn parse_pattern_nosubst<L: Language>(
    mut tok: &[Token],
) -> Result<(Pattern<L>, &[Token]), ParseError> {
    println!("parse_pattern_nosubst input tok = {:?}", tok);
    if let Token::PVar(p) = &tok[0] {
        let pat = Pattern::PVar(p.to_string());
        println!("parse_pattern_nosubst ret1 = {:?}", pat);
        return Ok((pat, &tok[1..]));
    }

    if let Token::LParen = tok[0] {
        tok = &tok[1..];

        let Token::Ident(op) = &tok[0] else {
            println!(
                "Error: parse_pattern_nosubst: expected Ident, got {:?}",
                tok[0]
            );
            return Err(ParseError::ParseState(to_vec(tok)));
        };
        tok = &tok[1..];

        let mut syntax_elems = vec![NestedSyntaxElem::String(op.to_string())];
        loop {
            if let Token::RParen = tok[0] {
                break;
            };

            let (se, tok2) = parse_nested_syntax_elem(tok)?;
            tok = tok2;
            syntax_elems.push(se);
        }
        tok = &tok[1..];

        let syntax_elems_mock: Vec<_> = syntax_elems
            .iter()
            .map(nested_syntax_elem_to_syntax_elem)
            .collect();
        println!("syntax_elems_mock = {:?}", syntax_elems_mock);
        println!("node = {:?}", L::from_syntax(&syntax_elems_mock));
        let node = L::from_syntax(&syntax_elems_mock)
            .ok_or_else(|| ParseError::FromSyntaxFailed(syntax_elems_mock))?;
        println!("node = {:?}", node);
        println!("syntax_elems = {:?}", syntax_elems);
        let syntax_elems = syntax_elems
            .into_iter()
            .filter_map(|x| {
                match x {
                    NestedSyntaxElem::Pattern(pat) => Some(pat),
                    NestedSyntaxElem::String(_) => None,
                    NestedSyntaxElem::Slot(_) => None,
                    // NestedSyntaxElem::Vec(_) => todo!(),
                    NestedSyntaxElem::Vec(_) => None,
                }
            })
            .collect();
        println!("transformed syntax_elems = {:?}", syntax_elems);
        let re = Pattern::ENode(node, syntax_elems);
        println!("parse_pattern_nosubst ret2 = {:?}", re);
        Ok((re, tok))
    } else {
        println!("second case");
        let Token::Ident(op) = &tok[0] else {
            println!(
                "Error: parse_pattern_nosubst: expected Ident2, got {:?}",
                tok[0]
            );
            return Err(ParseError::ParseState(to_vec(tok)));
        };
        tok = &tok[1..];

        let elems = [SyntaxElem::String(op.to_string())];
        let node =
            L::from_syntax(&elems).ok_or_else(|| ParseError::FromSyntaxFailed(to_vec(&elems)))?;
        let pat = Pattern::ENode(node, Vec::new());
        println!("parse_pattern_nosubst ret3 = {:?}", pat);
        Ok((pat, tok))
    }
}

// Like SyntaxElem, but contains Pattern instead of AppliedId.
#[derive(Debug, Clone)]
enum NestedSyntaxElem<L: Language> {
    Pattern(Pattern<L>),
    Vec(Vec<NestedSyntaxElem<L>>),
    Slot(Slot),
    String(String),
}

fn parse_nested_syntax_elem<L: Language>(
    tok: &[Token],
) -> Result<(NestedSyntaxElem<L>, &[Token]), ParseError> {
    println!("parse_nested_syntax_elem input tok = {:?}", tok);
    if let Token::LVecBracket = &tok[0] {
        // TODO(Pond)
        let mut ret: Vec<NestedSyntaxElem<L>> = Vec::new();
        let mut next = &tok[1..];
        loop {
            if let Token::RVecBracket = next[0] {
                break;
            }
            let (x, next2) = parse_nested_syntax_elem::<L>(next)?;
            next = next2;

            ret.push(x);
        }
        return Ok((NestedSyntaxElem::Vec(ret), &next[1..]));
    }

    if let Token::Slot(slot) = &tok[0] {
        println!(
            "parse_nested_syntax_elem ret = {:?}",
            NestedSyntaxElem::<L>::Slot(*slot)
        );
        return Ok((NestedSyntaxElem::Slot(*slot), &tok[1..]));
    }

    let recur_parse_result = parse_pattern::<L>(tok);
    let ret: Result<(NestedSyntaxElem<L>, &[Token]), ParseError> =
        recur_parse_result.map(|(x, rest)| (NestedSyntaxElem::Pattern(x), rest));
    println!("parse_nested_syntax_elem ret = {:?}", ret.clone());
    ret
}

fn to_vec<T: Clone>(t: &[T]) -> Vec<T> {
    t.iter().cloned().collect()
}
