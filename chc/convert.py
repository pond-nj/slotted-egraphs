"""Translate a small Prolog-style CHC dialect into SMT-LIB 2 (HORN logic).

The dialect is the one used by the VeriCaT / CAT benchmarks in
`chc/test/`: clauses of the form `Head :- Body.` (or `Head.`) where the
body is a comma-separated list of literals.  Each literal is either an
application of an uninterpreted predicate (e.g. `new7(M, N, A)`) or a
"constraint" formula built from:

    =>     boolean implication
    &      boolean conjunction
    ~      boolean negation       (`not(...)` is a synonym)
    =      polymorphic equality   (operands may be Int or Bool)
    =< >=  arithmetic comparisons
    <  >   arithmetic comparisons
    +  -   arithmetic
    [H|T]  list pattern (head Int, tail List)
    []     empty list

Operator precedence (lowest to highest): `=>`, `&`, `~`, comparison,
arith.  All paren-aware splitting is performed against `(` `)` and
`[` `]` together.
"""

from __future__ import annotations

import argparse
import re
import sys
from typing import Dict, List, Optional, Tuple


# ===========================================================================
# Paren-aware string utilities
# ===========================================================================


def split_top_level(text: str, sep: str) -> List[str]:
    """Split `text` at occurrences of `sep` that lie at paren-depth 0."""
    parts: List[str] = []
    buf: List[str] = []
    depth = 0
    i, n, sl = 0, len(text), len(sep)
    while i < n:
        c = text[i]
        if c in "([":
            depth += 1
            buf.append(c)
            i += 1
            continue
        if c in ")]":
            depth -= 1
            buf.append(c)
            i += 1
            continue
        if depth == 0 and text[i : i + sl] == sep:
            parts.append("".join(buf))
            buf = []
            i += sl
            continue
        buf.append(c)
        i += 1
    parts.append("".join(buf))
    return parts


def find_top_level_op(
    text: str, ops: List[str], rightmost: bool = False
) -> Tuple[int, Optional[str]]:
    """First (or last) top-level occurrence of any of `ops`.

    `ops` are tested in the given order at each position, so list the
    longer alternatives first (e.g. `["=<", ">=", "=", "<", ">"]`) to
    avoid `=` swallowing the head of `=<`.
    """
    depth = 0
    found: Tuple[int, Optional[str]] = (-1, None)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in "([":
            depth += 1
            i += 1
            continue
        if c in ")]":
            depth -= 1
            i += 1
            continue
        if depth == 0:
            matched: Optional[str] = None
            for op in ops:
                if text[i : i + len(op)] == op:
                    matched = op
                    break
            if matched is not None:
                if not rightmost:
                    return i, matched
                found = (i, matched)
                i += len(matched)
                continue
        i += 1
    return found


def strip_outer_parens(s: str) -> str:
    """Remove enclosing matched `(...)` (repeatedly), if any."""
    s = s.strip()
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        depth = 0
        ok = True
        for i, c in enumerate(s):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    ok = False
                    break
        if ok:
            s = s[1:-1].strip()
        else:
            break
    return s


def strip_comments(text: str) -> str:
    """Strip Prolog `% ...` line comments (outside string literals)."""
    out_lines = []
    for line in text.splitlines():
        i, n = 0, len(line)
        in_str = False
        quote = ""
        buf = []
        while i < n:
            c = line[i]
            if in_str:
                buf.append(c)
                if c == "\\" and i + 1 < n:
                    buf.append(line[i + 1])
                    i += 2
                    continue
                if c == quote:
                    in_str = False
            else:
                if c == "%":
                    break
                if c in ("'", '"'):
                    in_str = True
                    quote = c
                buf.append(c)
            i += 1
        out_lines.append("".join(buf))
    return "\n".join(out_lines)


def split_statements(text: str) -> List[str]:
    """Split Prolog source into top-level clauses (terminated by `. `)."""
    stmts: List[str] = []
    buf: List[str] = []
    depth = 0
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in "([":
            depth += 1
            buf.append(c)
            i += 1
            continue
        if c in ")]":
            depth -= 1
            buf.append(c)
            i += 1
            continue
        if (
            c == "."
            and depth == 0
            and (i + 1 >= n or text[i + 1].isspace() or text[i + 1] == "%")
        ):
            stmt = "".join(buf).strip()
            if stmt:
                stmts.append(stmt)
            buf = []
        else:
            buf.append(c)
        i += 1
    rest = "".join(buf).strip()
    if rest:
        stmts.append(rest)
    return stmts


# ===========================================================================
# AST
# ===========================================================================


class Var:
    __slots__ = ("name",)

    def __init__(self, name: str) -> None:
        self.name = name


class Num:
    __slots__ = ("val",)

    def __init__(self, val: int) -> None:
        self.val = val


class Nil:
    __slots__ = ()


class Cons:
    """List cons cell `[h | t]` where `h` and `t` are arbitrary terms."""

    __slots__ = ("h", "t")

    def __init__(self, h, t) -> None:
        self.h = h
        self.t = t


class Call:
    __slots__ = ("name", "args")

    def __init__(self, name: str, args: List) -> None:
        self.name = name
        self.args = args


class BinOp:
    __slots__ = ("op", "l", "r")

    def __init__(self, op: str, l, r) -> None:
        self.op = op
        self.l = l
        self.r = r


class Not:
    __slots__ = ("x",)

    def __init__(self, x) -> None:
        self.x = x


# ===========================================================================
# Parser
# ===========================================================================


_VAR_RE = re.compile(r"^[A-Z_][A-Za-z0-9_]*$")
_NUM_RE = re.compile(r"^-?\d+$")
_PRED_RE = re.compile(r"^([a-z][A-Za-z0-9_]*)\s*\((.*)\)$", re.DOTALL)
_BARE_PRED_RE = re.compile(r"^[a-z][A-Za-z0-9_]*$")


def _parse_list_literal(s: str):
    """Parse a Prolog list literal `[e1, e2, ... | Tail]` (Tail optional).

    Each element is parsed via `parse_term`; the optional tail (after `|`)
    is parsed via `parse_term` too (so it may be a variable, `[]`, or
    another nested list literal).
    """
    assert s.startswith("[") and s.endswith("]"), s
    inner = s[1:-1].strip()
    if not inner:
        return Nil()
    bar_pos, _ = find_top_level_op(inner, ["|"])
    if bar_pos == -1:
        elems_text = inner
        tail_node = Nil()
    else:
        elems_text = inner[:bar_pos]
        tail_node = parse_term(inner[bar_pos + 1 :].strip())
    elems = [parse_term(e) for e in split_top_level(elems_text, ",") if e.strip()]
    node = tail_node
    for e in reversed(elems):
        node = Cons(e, node)
    return node


def parse_term(s: str):
    """Parse a predicate-call argument: variable, integer, or list literal."""
    s = s.strip()
    if s == "[]":
        return Nil()
    if s.startswith("[") and s.endswith("]"):
        return _parse_list_literal(s)
    if _NUM_RE.match(s):
        return Num(int(s))
    if _VAR_RE.match(s):
        return Var(s)
    raise ValueError(f"unsupported predicate argument: {s!r}")


def parse_formula(s: str):
    """Recursive-descent parser for the constraint sub-language."""
    s = strip_outer_parens(s)
    if not s:
        raise ValueError("empty formula")

    # =>  (right-associative -> split at leftmost)
    pos, _ = find_top_level_op(s, ["=>"])
    if pos != -1:
        return BinOp("=>", parse_formula(s[:pos]), parse_formula(s[pos + 2 :]))

    # &  (associative -> leftmost is fine)
    pos, _ = find_top_level_op(s, ["&"])
    if pos != -1:
        return BinOp("&", parse_formula(s[:pos]), parse_formula(s[pos + 1 :]))

    # leading ~
    s2 = s.lstrip()
    if s2.startswith("~"):
        return Not(parse_formula(s2[1:]))

    # comparison (longest match first; `=<` and `>=` before `=`/`<`/`>`)
    pos, op = find_top_level_op(s, ["=<", ">=", "=", "<", ">"])
    if pos != -1 and op is not None:
        return BinOp(op, parse_formula(s[:pos]), parse_formula(s[pos + len(op) :]))

    # arithmetic + / -  (left-associative -> split at rightmost)
    pos, op = find_top_level_op(s, ["+", "-"], rightmost=True)
    if pos != -1 and op is not None:
        return BinOp(op, parse_formula(s[:pos]), parse_formula(s[pos + 1 :]))

    # atomic
    s = s.strip()
    if s == "[]":
        return Nil()
    if s.startswith("[") and s.endswith("]"):
        return _parse_list_literal(s)
    if _NUM_RE.match(s):
        return Num(int(s))
    if _VAR_RE.match(s):
        return Var(s)
    m = _PRED_RE.match(s)
    if m:
        name = m.group(1)
        inner = m.group(2).strip()
        if name == "not":
            inside = split_top_level(inner, ",")
            if len(inside) != 1:
                raise ValueError(f"not/{len(inside)} unsupported: {s!r}")
            return Not(parse_formula(inside[0]))
        if name == "constr":
            # `constr(F)` wraps an embedded constraint formula; unwrap it.
            inside = split_top_level(inner, ",")
            if len(inside) != 1:
                raise ValueError(f"constr/{len(inside)} unsupported: {s!r}")
            return parse_formula(inside[0])
        if not inner:
            return Call(name, [])
        args = [parse_term(a) for a in split_top_level(inner, ",") if a.strip()]
        return Call(name, args)
    if _BARE_PRED_RE.match(s):
        return Call(s, [])
    raise ValueError(f"cannot parse formula: {s!r}")


class Clause:
    __slots__ = ("head", "body", "src")

    def __init__(self, head: Call, body: List, src: str = "") -> None:
        self.head = head
        self.body = body
        self.src = src


def parse_clause(stmt: str) -> Clause:
    pos, _ = find_top_level_op(stmt, [":-"])
    if pos == -1:
        head_s, body_s = stmt.strip(), ""
    else:
        head_s, body_s = stmt[:pos].strip(), stmt[pos + 2 :].strip()
    head_node = parse_formula(head_s)
    if not isinstance(head_node, Call):
        raise ValueError(f"clause head is not a predicate call: {head_s!r}")
    body_parts = [p.strip() for p in split_top_level(body_s, ",") if p.strip()]
    body = [parse_formula(p) for p in body_parts]
    return Clause(head_node, body, stmt.strip() + ".")


# ===========================================================================
# Type inference
# ===========================================================================


INT, BOOL, LIST_T = "Int", "Bool", "List"
_PRIO = {None: 0, INT: 1, LIST_T: 2, BOOL: 3}


def _merge(a: Optional[str], b: Optional[str]) -> Optional[str]:
    return a if _PRIO[a] >= _PRIO[b] else b


def infer_types(
    clauses: List[Clause],
) -> Tuple[List[Dict[str, str]], Dict[str, List[str]]]:
    """Infer per-clause variable types and per-predicate argument types.

    Iterates a monotone propagation over Bool > List > Int > unknown
    until reaching a fixed point.
    """
    pred_arg_types: Dict[str, List[Optional[str]]] = {}

    # Seed with arities from heads.
    for cl in clauses:
        nm, ar = cl.head.name, len(cl.head.args)
        if nm not in pred_arg_types:
            pred_arg_types[nm] = [None] * ar
        elif len(pred_arg_types[nm]) != ar:
            raise ValueError(f"arity mismatch for predicate `{nm}`")

    per_clause: List[Dict[str, Optional[str]]] = [{} for _ in clauses]

    def set_var(d: Dict[str, Optional[str]], v: str, t: Optional[str]) -> bool:
        old = d.get(v)
        new = _merge(old, t)
        if new != old:
            d[v] = new
            return True
        return False

    def set_pred(p: str, i: int, t: Optional[str]) -> bool:
        cur = pred_arg_types[p][i]
        new = _merge(cur, t)
        if new != cur:
            pred_arg_types[p][i] = new
            return True
        return False

    def type_of(node, vt: Dict[str, Optional[str]]) -> Optional[str]:
        if isinstance(node, Num):
            return INT
        if isinstance(node, (Nil, Cons)):
            return LIST_T
        if isinstance(node, Var):
            return vt.get(node.name)
        if isinstance(node, Not):
            return BOOL
        if isinstance(node, BinOp):
            if node.op in ("=>", "&", "=<", ">=", "<", ">", "="):
                return BOOL
            return INT  # +, -
        if isinstance(node, Call):
            return BOOL
        return None

    def visit(node, vt: Dict[str, Optional[str]], expected: Optional[str]) -> bool:
        changed = False
        if isinstance(node, Var):
            if expected is not None:
                changed |= set_var(vt, node.name, expected)
        elif isinstance(node, (Num, Nil)):
            pass
        elif isinstance(node, Cons):
            changed |= visit(node.h, vt, INT)
            changed |= visit(node.t, vt, LIST_T)
        elif isinstance(node, Not):
            changed |= visit(node.x, vt, BOOL)
        elif isinstance(node, BinOp):
            op = node.op
            if op in ("=>", "&"):
                changed |= visit(node.l, vt, BOOL)
                changed |= visit(node.r, vt, BOOL)
            elif op in ("=<", ">=", "<", ">", "+", "-"):
                changed |= visit(node.l, vt, INT)
                changed |= visit(node.r, vt, INT)
            elif op == "=":
                lt = type_of(node.l, vt)
                rt = type_of(node.r, vt)
                t = _merge(lt, rt)
                changed |= visit(node.l, vt, t)
                changed |= visit(node.r, vt, t)
        elif isinstance(node, Call):
            if not node.args:
                return changed
            if node.name not in pred_arg_types:
                pred_arg_types[node.name] = [None] * len(node.args)
            sig = pred_arg_types[node.name]
            if len(sig) != len(node.args):
                raise ValueError(f"arity mismatch on call to `{node.name}`")
            for i, a in enumerate(node.args):
                if isinstance(a, Var):
                    expected_i = _merge(sig[i], vt.get(a.name))
                    changed |= set_var(vt, a.name, expected_i)
                    changed |= set_pred(node.name, i, vt.get(a.name))
                elif isinstance(a, Num):
                    changed |= set_pred(node.name, i, INT)
                elif isinstance(a, Nil):
                    changed |= set_pred(node.name, i, LIST_T)
                elif isinstance(a, Cons):
                    changed |= set_pred(node.name, i, LIST_T)
                    changed |= visit(a, vt, LIST_T)
        return changed

    # Fixed-point iteration.
    for _ in range(64):
        changed = False
        for cl, vt in zip(clauses, per_clause):
            sig = pred_arg_types[cl.head.name]
            for i, a in enumerate(cl.head.args):
                if isinstance(a, Var):
                    cur = _merge(sig[i], vt.get(a.name))
                    changed |= set_var(vt, a.name, cur)
                    changed |= set_pred(cl.head.name, i, vt.get(a.name))
                elif isinstance(a, Num):
                    changed |= set_pred(cl.head.name, i, INT)
                elif isinstance(a, Nil):
                    changed |= set_pred(cl.head.name, i, LIST_T)
                elif isinstance(a, Cons):
                    changed |= set_pred(cl.head.name, i, LIST_T)
                    changed |= visit(a, vt, LIST_T)
            for lit in cl.body:
                changed |= visit(lit, vt, BOOL)
        if not changed:
            break

    # Default any unresolved type to Int.
    final_pred: Dict[str, List[str]] = {
        nm: [t if t is not None else INT for t in ts]
        for nm, ts in pred_arg_types.items()
    }
    final_clause: List[Dict[str, str]] = [
        {v: (t if t is not None else INT) for v, t in vt.items()} for vt in per_clause
    ]
    return final_clause, final_pred


# ===========================================================================
# SMT-2 emission
# ===========================================================================


_SMT_OP = {
    "=>": "=>",
    "&": "and",
    "=": "=",
    "=<": "<=",
    ">=": ">=",
    "<": "<",
    ">": ">",
    "+": "+",
    "-": "-",
}


def emit(node) -> str:
    if isinstance(node, Var):
        return node.name
    if isinstance(node, Num):
        return str(node.val) if node.val >= 0 else f"(- {-node.val})"
    if isinstance(node, Nil):
        return "mk-nil"
    if isinstance(node, Cons):
        return f"(mk-cons {emit(node.h)} {emit(node.t)})"
    if isinstance(node, Not):
        return f"(not {emit(node.x)})"
    if isinstance(node, BinOp):
        return f"({_SMT_OP[node.op]} {emit(node.l)} {emit(node.r)})"
    if isinstance(node, Call):
        if not node.args:
            return node.name
        return f"({node.name} {' '.join(emit(a) for a in node.args)})"
    raise TypeError(f"cannot emit node: {node!r}")


def _collect_vars(node, out: Dict[str, None]) -> None:
    if isinstance(node, Var):
        out[node.name] = None
    elif isinstance(node, Cons):
        _collect_vars(node.h, out)
        _collect_vars(node.t, out)
    elif isinstance(node, Not):
        _collect_vars(node.x, out)
    elif isinstance(node, BinOp):
        _collect_vars(node.l, out)
        _collect_vars(node.r, out)
    elif isinstance(node, Call):
        for a in node.args:
            _collect_vars(a, out)


def to_smt2(clauses: List[Clause], query_pred: str) -> str:
    per_clause, pred_types = infer_types(clauses)

    out: List[str] = []
    out.append("(set-logic HORN)")
    out.append(
        "(declare-datatypes () " "((List (mk-nil) (mk-cons (head Int) (tail List)))))"
    )
    for nm in sorted(pred_types):
        if nm == query_pred:
            continue
        out.append(f"(declare-fun {nm} ({' '.join(pred_types[nm])}) Bool)")

    for cl, vt in zip(clauses, per_clause):
        # Collect variables for the universal quantifier (preserve insertion order).
        used: Dict[str, None] = {}
        for a in cl.head.args:
            _collect_vars(a, used)
        for lit in cl.body:
            _collect_vars(lit, used)

        var_decls = " ".join(f"({v} {vt.get(v, INT)})" for v in used)

        if cl.body:
            body_smt = "(and " + " ".join(emit(l) for l in cl.body) + ")"
        else:
            body_smt = "true"

        if cl.head.name == query_pred:
            inner = f"(not {body_smt})"
        else:
            inner = f"(=> {body_smt} {emit(cl.head)})"

        if cl.src:
            for line in cl.src.splitlines():
                out.append(f"; {line}")
        if var_decls:
            out.append(f"(assert (forall ({var_decls}) {inner}))")
        else:
            out.append(f"(assert {inner})")

    out.append("(check-sat)")
    return "\n".join(out) + "\n"


# ===========================================================================
# Driver
# ===========================================================================


def prolog_to_smt2_chc(prolog_code: str, query_pred: str = "false") -> str:
    """High-level entry point used by the CLI and importers.

    `query_pred` names the Prolog predicate that should be treated as the
    Horn-clause query: every clause whose head is that predicate is
    emitted as `(assert (forall ... (not body)))` instead of an
    implication, i.e. its head is interpreted as boolean `false` in the
    resulting SMT script.
    """
    statements = split_statements(strip_comments(prolog_code))
    clauses: List[Clause] = []
    for st in statements:
        if st.startswith(":-"):
            # Directive (e.g., `:- dynamic foo/2.`) -- ignored.
            continue
        clauses.append(parse_clause(st))
    return to_smt2(clauses, query_pred)


def _main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        description="Translate a Prolog-style CHC file into SMT-LIB 2 (HORN logic).",
    )
    ap.add_argument(
        "input",
        help="input Prolog CHC file (use `-` for stdin)",
    )
    ap.add_argument(
        "-o",
        "--output",
        help="output SMT-2 file (default: stdout)",
    )
    ap.add_argument(
        "-q",
        "--query",
        default="false",
        help=(
            "name of the predicate to be treated as the Horn-clause query; "
            "clauses whose head matches this name are emitted as the negated "
            "body (i.e. the head is interpreted as boolean `false`). "
            "Default: %(default)s."
        ),
    )
    args = ap.parse_args(argv)

    if args.input == "-":
        prolog_code = sys.stdin.read()
    else:
        with open(args.input) as f:
            prolog_code = f.read()

    smt = prolog_to_smt2_chc(prolog_code, query_pred=args.query)

    if args.output:
        with open(args.output, "w") as f:
            f.write(smt)
    else:
        sys.stdout.write(smt)
    return 0


if __name__ == "__main__":
    sys.exit(_main())
