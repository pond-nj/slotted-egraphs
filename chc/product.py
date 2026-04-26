#!/usr/bin/env python3
"""
product.py
==========

Implementation of the CHC product transformation from

    "Synchronizing Constrained Horn Clauses",
    Dmitry Mordvinov and Grigory Fedyukovich,
    LPAR-21, 2017  (papers/product.pdf)

Given a Prolog-style CHC file (the format used by the VeriCaT benchmarks)
and a list of predicate symbols p1, p2, ..., pn (n >= 2), this script
builds the n-ary product predicate `p1 x ... x pn` (Def. 13), generates
its rules by taking the cartesian product of `rules(p_i)` and combining
them according to Def. 12, and rewrites every clause whose body contains
an application of each p_i (in any order) so that those applications are
replaced by a single application of the new product predicate (Def. 14).

This is the "inner" step of Algorithm 1 in the paper.  Re-running the
script on its own output performs the worklist iterations.

Usage
-----
    python3 product.py INPUT.pl PRED1 PRED2 [PRED3 ...]
                       [-o OUTPUT.pl] [-n NEW_NAME]

Limitations
-----------
* The Prolog parser is intentionally small.  It handles the subset of
  syntax appearing in the VeriCaT/MAP-style benchmark files: clauses of
  the form `Head :- Body.` (or `Head.`), directives `:- ...`, line
  comments `% ...`, and predicate applications of the form `name(...)`.
* "Constraints" are any body literals whose functor is not one of the
  uninterpreted predicates being merged; their text is preserved
  verbatim apart from variable renaming.
* Applications p_i and p_j must be distinct (Def. 14 forbids self
  products).  To take the product of a predicate with itself, first
  rename one copy.
"""

from __future__ import annotations

import argparse
import re
import sys
from itertools import product as cart_product
from typing import List, Optional, Tuple


# --------------------------------------------------------------------------
# Lexical helpers
# --------------------------------------------------------------------------

# Matches a Prolog variable token (uppercase or `_` start) at a token
# boundary.  The negative look-behind keeps us from chopping the tail of
# an identifier.
_VAR_RE = re.compile(r"(?<![A-Za-z0-9_])([A-Z_][A-Za-z0-9_]*)")

# A bare atom (lowercase identifier) optionally followed by `(args)`.
_ATOM_CALL_RE = re.compile(r"^\s*([a-z][A-Za-z0-9_]*)\s*\((.*)\)\s*$", re.DOTALL)
_ATOM_BARE_RE = re.compile(r"^\s*([a-z][A-Za-z0-9_]*)\s*$")


def strip_comments(text: str) -> str:
    """Remove Prolog-style line comments (`% ...`) outside string literals."""
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
    """Split text into top-level statements, terminated by `.` whitespace."""
    stmts: List[str] = []
    buf: List[str] = []
    depth = 0
    in_str = False
    quote = ""
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if in_str:
            buf.append(c)
            if c == "\\" and i + 1 < n:
                buf.append(text[i + 1])
                i += 2
                continue
            if c == quote:
                in_str = False
            i += 1
            continue
        if c in ("'", '"'):
            in_str = True
            quote = c
            buf.append(c)
        elif c in "([":
            depth += 1
            buf.append(c)
        elif c in ")]":
            depth -= 1
            buf.append(c)
        elif (
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


def split_top_level(text: str, sep: str = ",") -> List[str]:
    """Split `text` at occurrences of `sep` that lie at parenthesis depth 0."""
    parts: List[str] = []
    buf: List[str] = []
    depth = 0
    in_str = False
    quote = ""
    i, n = 0, len(text)
    sl = len(sep)
    while i < n:
        c = text[i]
        if in_str:
            buf.append(c)
            if c == "\\" and i + 1 < n:
                buf.append(text[i + 1])
                i += 2
                continue
            if c == quote:
                in_str = False
            i += 1
            continue
        if c in ("'", '"'):
            in_str = True
            quote = c
            buf.append(c)
            i += 1
            continue
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
            parts.append("".join(buf).strip())
            buf = []
            i += sl
            continue
        buf.append(c)
        i += 1
    last = "".join(buf).strip()
    if last or parts:
        parts.append(last)
    return parts


def find_top_level(text: str, needle: str) -> int:
    """Return the index of the first top-level occurrence of `needle`, or -1."""
    depth = 0
    in_str = False
    quote = ""
    i, n = 0, len(text)
    nl = len(needle)
    while i < n:
        c = text[i]
        if in_str:
            if c == "\\" and i + 1 < n:
                i += 2
                continue
            if c == quote:
                in_str = False
            i += 1
            continue
        if c in ("'", '"'):
            in_str = True
            quote = c
            i += 1
            continue
        if c in "([":
            depth += 1
            i += 1
            continue
        if c in ")]":
            depth -= 1
            i += 1
            continue
        if depth == 0 and text[i : i + nl] == needle:
            return i
        i += 1
    return -1


# --------------------------------------------------------------------------
# Term / clause representation
# --------------------------------------------------------------------------


def parse_term(text: str) -> Tuple[Optional[str], List[str]]:
    """Return (functor, args) for an applied or atomic term.

    For a 0-ary atom the args list is empty.  For anything that does not
    look like an applied atom (e.g. a constraint expression `H =< T`),
    returns (None, []).
    """
    text = text.strip()
    m = _ATOM_CALL_RE.match(text)
    if m:
        functor = m.group(1)
        args = split_top_level(m.group(2), ",")
        return functor, args
    m2 = _ATOM_BARE_RE.match(text)
    if m2:
        return m2.group(1), []
    return None, []


class Literal:
    __slots__ = ("text", "functor", "args")

    def __init__(self, text: str):
        self.text = text.strip()
        self.functor, self.args = parse_term(self.text)

    def __repr__(self) -> str:
        return f"Literal({self.text!r})"


class Clause:
    """A CHC `Head :- L1, ..., Lk.` (or a fact `Head.`)."""

    def __init__(self, raw: str):
        self.raw = raw.strip()
        idx = find_top_level(self.raw, ":-")
        if idx == -1:
            head_text, body_text = self.raw, ""
        else:
            head_text = self.raw[:idx].strip()
            body_text = self.raw[idx + 2 :].strip()
        self.head = Literal(head_text)
        if body_text:
            self.body = [
                Literal(t) for t in split_top_level(body_text, ",") if t.strip()
            ]
        else:
            self.body = []

    @property
    def variables(self) -> set:
        names = set()
        for s in [self.head.text] + [l.text for l in self.body]:
            for v in _VAR_RE.findall(s):
                if v != "_":
                    names.add(v)
        return names

    def render(self) -> str:
        if not self.body:
            return f"{self.head.text}."
        return (
            f"{self.head.text} :-\n    "
            + ",\n    ".join(l.text for l in self.body)
            + "."
        )


# --------------------------------------------------------------------------
# The product transformation
# --------------------------------------------------------------------------


def rename_text(text: str, mapping: dict) -> str:
    """Rename whole-token variables in `text` according to `mapping`."""

    def repl(m):
        v = m.group(1)
        return mapping.get(v, v)

    return _VAR_RE.sub(repl, text)


def make_call(name: str, args: List[str]) -> str:
    if not args:
        return name
    return f"{name}({', '.join(args)})"


def product_rule(
    combo: Tuple[Clause, ...], target_preds: List[str], new_name: str
) -> Optional[str]:
    """Build one rule of `new_name` from a tuple `(C_1, ..., C_n)` where
    `C_i in rules(p_i)`.  Implements Def. 12 directly.
    """
    # 1. Rename each clause's variables so the n bodies are variable-disjoint
    #    (Remark 1 in the paper).
    renamed_heads: List[str] = []
    renamed_bodies: List[List[str]] = []
    for i, cl in enumerate(combo):
        suffix = str(i + 1)
        mapping = {v: f"{v}_{suffix}" for v in cl.variables}
        renamed_heads.append(rename_text(cl.head.text, mapping))
        renamed_bodies.append([rename_text(l.text, mapping) for l in cl.body])

    # 2. Product head: concatenate the argument vectors of head(C_i).
    head_args: List[str] = []
    for h in renamed_heads:
        _, args = parse_term(h)
        head_args.extend(args)
    new_head = make_call(new_name, head_args)

    # 3. Categorise body literals of each renamed clause:
    #      L_i  - non-recursive applications and constraints
    #      R_i  - recursive applications (functor == p_i)
    L_lits: List[str] = []
    R_choices: List[List[List[str]]] = []
    for i, body in enumerate(renamed_bodies):
        p_i = target_preds[i]
        rec_argvecs: List[List[str]] = []
        for bt in body:
            f, a = parse_term(bt)
            if f == p_i:
                rec_argvecs.append(a)
            else:
                L_lits.append(bt)
        if not rec_argvecs:
            # Tautological extension of a fact (Def. 11): R/head(C_i) = {head(C_i)}.
            _, head_args_i = parse_term(renamed_heads[i])
            rec_argvecs = [head_args_i]
        R_choices.append(rec_argvecs)

    # 4. Build the recursive part of the product body.  Coverage chosen as
    #    the full cartesian product (which trivially covers, see Def. 9).
    R_calls: List[str] = []
    for tup in cart_product(*R_choices):
        merged_args: List[str] = []
        for a in tup:
            merged_args.extend(a)
        R_calls.append(make_call(new_name, merged_args))

    # 5. Per Def. 12, drop head(C) from R (i.e. avoid the trivial self loop
    #    that would arise when every C_i is a fact).
    R_calls = [c for c in R_calls if c != new_head]

    body_parts = R_calls + L_lits
    if not body_parts:
        return f"{new_head}."
    return f"{new_head} :-\n    " + ",\n    ".join(body_parts) + "."


def build_product_rules(
    clauses: List[Clause], target_preds: List[str], new_name: str
) -> List[str]:
    rules_of = {p: [c for c in clauses if c.head.functor == p] for p in target_preds}
    for p, rs in rules_of.items():
        if not rs:
            print(f"warning: no rules found for predicate `{p}`", file=sys.stderr)

    new_rules: List[str] = []
    for combo in cart_product(*[rules_of[p] for p in target_preds]):
        r = product_rule(combo, target_preds, new_name)
        if r is not None:
            new_rules.append(r)
    return new_rules


def replace_conjunction(
    clause: Clause, target_preds: List[str], new_name: str
) -> Optional[str]:
    """If `clause` body has at least one application of each p_i, replace the
    first occurrence of each by a single product call (Def. 14).  Returns
    the rewritten clause text, or None if the clause is unchanged.

    To stay faithful to the paper's hypothesis that p_1, ..., p_n are
    pairwise different and different from rel(head(C)), we also refuse to
    rewrite a clause whose own head is one of the target predicates.
    """
    if clause.head.functor in target_preds:
        return None
    first_index: dict = {}
    for i, lit in enumerate(clause.body):
        if lit.functor in target_preds and lit.functor not in first_index:
            first_index[lit.functor] = i
    if any(p not in first_index for p in target_preds):
        return None

    drop = set(first_index.values())
    insert_at = min(first_index.values())
    merged_args: List[str] = []
    for p in target_preds:
        merged_args.extend(clause.body[first_index[p]].args)
    merged_call = make_call(new_name, merged_args)

    new_body: List[str] = []
    for i, lit in enumerate(clause.body):
        if i == insert_at:
            new_body.append(merged_call)
        elif i in drop:
            continue
        else:
            new_body.append(lit.text)

    if not new_body:
        return f"{clause.head.text}."
    return f"{clause.head.text} :-\n    " + ",\n    ".join(new_body) + "."


# --------------------------------------------------------------------------
# Driver
# --------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser(
        description=(
            "Apply the CHC product transformation of "
            "Mordvinov & Fedyukovich (LPAR-21, 2017) to a Prolog CHC file."
        )
    )
    ap.add_argument("input", help="input Prolog CHC file")
    ap.add_argument(
        "predicates", nargs="+", help="predicates to take the product of (>= 2)"
    )
    ap.add_argument("-o", "--output", help="output file (default: stdout)")
    ap.add_argument(
        "-n", "--name", help="name of the product predicate " "(default: p1_x_p2_x_...)"
    )
    args = ap.parse_args()

    if len(args.predicates) < 2:
        ap.error("need at least 2 predicates to take a product")
    if len(set(args.predicates)) != len(args.predicates):
        ap.error(
            "the paper's Def. 14 forbids self-products; "
            "make the predicate names distinct first"
        )

    new_name = args.name or "_x_".join(args.predicates)

    with open(args.input) as f:
        src = f.read()

    statements = split_statements(strip_comments(src))

    directives: List[str] = []
    clauses: List[Clause] = []
    for st in statements:
        if st.startswith(":-"):
            directives.append(st + ".")
            continue
        cl = Clause(st)
        if cl.head.functor is None:
            # Could not parse a head; preserve as-is.
            directives.append(st + ".")
        else:
            clauses.append(cl)

    new_rules = build_product_rules(clauses, args.predicates, new_name)

    rewritten_clauses: List[str] = []
    n_rewritten = 0
    for cl in clauses:
        out = replace_conjunction(cl, args.predicates, new_name)
        if out is not None:
            rewritten_clauses.append(out)
            n_rewritten += 1
        else:
            rewritten_clauses.append(cl.render())

    out_lines: List[str] = []
    out_lines.append("% =============================================================")
    out_lines.append(
        "% CHC product transformation" f" of: {', '.join(args.predicates)}"
    )
    out_lines.append(f"% Product predicate: {new_name}")
    out_lines.append(f"% Rewritten clauses: {n_rewritten}")
    out_lines.append(f"% Generated rules:   {len(new_rules)}")
    out_lines.append("% =============================================================")
    out_lines.append("")
    if directives:
        for d in directives:
            out_lines.append(d)
        out_lines.append("")
    out_lines.append(f"% --- rules of the product predicate `{new_name}` ---")
    out_lines.append("")
    for r in new_rules:
        out_lines.append(r)
        out_lines.append("")
    out_lines.append("% --- (rewritten) original clauses ---")
    out_lines.append("")
    for c in rewritten_clauses:
        out_lines.append(c)
        out_lines.append("")

    output = "\n".join(out_lines)
    if args.output:
        with open(args.output, "w") as f:
            f.write(output)
        print(
            f"wrote {args.output} "
            f"({len(new_rules)} new rules, {n_rewritten} rewritten clauses)",
            file=sys.stderr,
        )
    else:
        sys.stdout.write(output)
    return 0


if __name__ == "__main__":
    sys.exit(main())
