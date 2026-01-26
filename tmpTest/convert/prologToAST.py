# parse a prolog body
from collections import defaultdict
import json
import re
from ast import CHC, Constr, ConstrOP, PredApp, Var

import pprint
from typing import Optional


# group lines by .
def groupLines(lines):
    newLines = []
    currLine = ""
    for line in lines:
        line = line.replace("\n", "")
        for c in line:
            if c == ".":
                newLines.append(currLine + c)
                currLine = ""
            else:
                currLine += c
    if currLine != "":
        newLines.append(currLine)

    return newLines


def parseBody(expression):
    # B1, B2, B3 into [B1, B2, B3]
    """Split a Prolog expression into individual components."""
    result = []
    current = ""
    bracket_count = 0

    for char in expression:
        if char == "(":
            bracket_count += 1
            current += char
        elif char == ")":
            bracket_count -= 1
            current += char
        elif char == "," and bracket_count == 0:
            # Only split on commas outside of brackets
            result.append(current.strip())
            current = ""
        else:
            current += char

    # Add the last component
    if current.strip():
        result.append(current.strip())

    return result


def parseProlog(lines) -> list[CHC]:
    chcs: list[CHC] = []

    for line in lines:
        line = line.strip()
        if line.startswith("%"):
            continue

        if line.startswith("#t"):
            continue
        if line == "":
            continue

        if line[-1] == ".":
            line = line[:-1]

        if not ":-" in line:
            assert re.match(r"^(\w*)\((.*)\)$", line)
            head = line
            body = ""
        else:
            head, body = line.split(":-")
            head = head.strip()
            body = body.strip()

        headPred = head.split("(")[0]
        # assert headPred in headType
        if "(" in head:
            assert re.match(r"^(\w*)\((.*)\)$", head)

            def prep(x):
                x = x.strip()
                return parseConstr(x)

            headArgs = list(
                map(lambda x: prep(x), head.split("(")[1].split(")")[0].split(","))
            )
        else:
            headArgs = []

        constr: list[Constr] = []

        body = parseBody(body)

        predapps: list[PredApp] = []
        for b in body:
            b = b.strip()
            res = re.match(r"^(\w*)\((.*)\)$", b)
            if res:
                bPred = res.group(1)

                def prep(x):
                    x = x.strip()
                    return parseConstr(x)

                bArgs = list(map(prep, res.group(2).split(",")))
                predapps.append(PredApp(bPred, bArgs))
            else:
                parsedC = parseConstr(b)
                if parsedC is not None:
                    assert isinstance(parsedC, Constr)
                    constr.append(parsedC)

        chcs.append(
            CHC(
                PredApp(headPred, headArgs),
                constr,
                predapps,
                line,
            )
        )
    return chcs


def parse(fname) -> list[CHC]:
    f = open(fname, "r")
    lines = f.readlines()

    newLines = groupLines(lines)
    return parseProlog(newLines)


def parseConstr(constr: str) -> Constr | Var:
    origConstr = constr
    constr = constr.strip()

    if constr.isnumeric():
        print(f"parseConstr {origConstr} -> [{int(constr)}]")
        return Var(int(constr))

    if re.match(r"^\w+$", constr):
        print(f"parseConstr {origConstr} -> [{constr}]")
        return Var(constr)

    if constr == "[]":
        print(f"parseConstr {origConstr} -> [{ConstrOP.emptyList}]")
        return Constr(ConstrOP.emptyList, [])

    if constr[0] == "[" and constr[-1] == "]":
        constr = constr[1:-1]
        if "|" in constr:
            assert constr.count("|") == 1
            left, right = constr.split("|")
            print(
                f"parseConstr {origConstr} -> [{ConstrOP.list}, {parseConstr(left)}, {parseConstr(right)}]"
            )
            return Constr(ConstrOP.list, [parseConstr(left), parseConstr(right)])
        else:
            assert re.match(r"^\w+$", constr)
            print(
                f"parseConstr {origConstr} -> [{ConstrOP.list}, {parseConstr(constr)}, {ConstrOP.emptyList}]"
            )
            return Constr(
                ConstrOP.list, [parseConstr(constr), Constr(ConstrOP.emptyList, [])]
            )

    res = re.match(r"^node\((.*)\)$", constr)
    if res:
        print("match found")
        args = res.group(1).split(",")
        assert len(args) == 3
        print(
            f"parseConstr {origConstr} -> [{ConstrOP.binode}, {parseConstr(args[0])}, {parseConstr(args[1])}, {parseConstr(args[2])}]"
        )
        return Constr(
            ConstrOP.binode,
            [parseConstr(args[0]), parseConstr(args[1]), parseConstr(args[2])],
        )

    first, constr = constrGetNextTerm(constr)
    opStr, constr = constrGetNextTerm(constr)
    children = []
    try:
        op = ConstrOP(opStr)
        children.append(parseConstr(first))
        children.append(parseConstr(constr))
    except KeyError:
        raise Exception(f"opStr {opStr} not found")

    print(f"parseConstr {origConstr} -> {children}")
    return Constr(op, children)


def constrGetNextTerm(constr):
    constr = constr.strip()
    i = 0
    bracket_count = 0

    firstIsVarNotOp = False
    if constr[0].isalpha() or constr[0].isdigit():
        firstIsVarNotOp = True

    while i < len(constr):
        if constr[i] == " " and bracket_count == 0:
            break

        if (
            firstIsVarNotOp
            and (not constr[i].isalpha() and not constr[i].isdigit())
            and bracket_count == 0
        ):
            break

        if (
            not firstIsVarNotOp
            and (constr[i].isalpha() or constr[i].isdigit())
            and bracket_count == 0
        ):
            break

        if constr[i] == "(":
            bracket_count += 1
        elif constr[i] == ")":
            bracket_count -= 1
        elif constr[i] == "[":
            bracket_count += 1
        elif constr[i] == "]":
            bracket_count -= 1
        i += 1
    print(
        "constrGetNextTerm",
        f"{{{constr}}}",
        "->",
        f"{{{constr[:i]}}}",
        f"{{{constr[i:]}}}",
    )
    return constr[:i], constr[i:]


struct = parse("prologInp.txt")

for chc in struct:
    chc.renameHead()
