# input
# append(X, Y, Z) :- X = [], Y = Z.
# append(X, Y, Z) :- X = [T|X1], Z = [T|Z1], append(X1, Y, Z1).

from collections import defaultdict
from enum import Enum
import pprint
import re


def parseBody(expression):
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


def parseProlog(lines):
    """
    list of dict[predName -> list[rule]]
    where rule = {
        "headArgs",
        "constr",
        "dependencies",
        "line",
    }
    """
    ret = defaultdict(list)
    predNameToHeadArgs = {}
    for line in lines:
        rule = {}
        line = line.strip()
        if line.startswith("%"):
            continue

        if line == "":
            continue

        if line[-1] == ".":
            line = line[:-1]

        head, body = line.split(":-")
        head = head.strip()
        body = body.strip()

        headPred = head.split("(")[0]
        headArgs = list(
            map(lambda x: x.strip(), head.split("(")[1].split(")")[0].split(","))
        )

        body = parseBody(body)
        print("body", body)
        constr = []
        dependencies = []
        for b in body:
            print(b)
            b = b.strip()
            if re.match(r"^(\w*)\((.*)\)$", b):
                dependencies.append(b)
            else:
                constr.append(b)
        rule = {
            "headArgs": headArgs,
            "constr": constr,
            "dependencies": dependencies,
            "line": line,
        }
        ret[headPred].append(rule)
        if headPred not in predNameToHeadArgs:
            predNameToHeadArgs[headPred] = headArgs
        else:
            print(predNameToHeadArgs[headPred])
            print(headArgs)
            assert predNameToHeadArgs[headPred] == headArgs
    return ret


class OP(Enum):
    eq = "="
    add = "+"
    minus = "-"
    leq = "=<"
    geq = ">="
    less = "<"
    greater = ">"
    emptyList = "[]"
    list = "list"
    binode = "node"


def constrGetNextTerm(constr):
    constr = constr.strip()
    i = 0
    bracket_count = 0
    firstType = None

    firstIsVarNotOp = False
    if constr[0].isalpha() or constr[0].isdigit():
        firstIsVarNotOp = True

    while i < len(constr):
        if constr[i] == " " and bracket_count == 0:
            break

        if firstIsVarNotOp and (not constr[i].isalpha() and not constr[i].isdigit()):
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


def unwrapParse(t):
    res = parseConstr(t)
    if len(res) == 1:
        return res[0]

    return res


def parseConstr(constr):
    constr = constr.strip()
    tree = []
    print("parseConstr", constr)

    if constr == "":
        return []

    if re.match(r"^\w+$", constr):
        return [constr]

    if constr == "[]":
        return [OP.emptyList]

    first, constr = constrGetNextTerm(constr)
    if first[0] == "[" and first[1] != "]":
        assert first[-1] == "]"
        first = first[1:-1]
        assert "|" in first
        assert first.count("|") == 1
        left, right = first.split("|")
        tree.append(OP.list)
        tree.append(unwrapParse(left))
        tree.append(unwrapParse(right))
    elif first.startswith("node"):
        assert first.endswith(")")
        first = first[:-1]
        assert first.startswith("node(")
        first = first[5:]
        tree.append(OP.node)
        first = first.split(",")
        assert len(first) == 3
        tree.append(unwrapParse(first[0]))
        tree.append(unwrapParse(first[1]))
        tree.append(unwrapParse(first[2]))
    else:
        opStr, constr = constrGetNextTerm(constr)
        try:
            op = OP(opStr)
            tree.append(op)
            tree.append(first)
            tree.append(unwrapParse(constr))
        except KeyError:
            raise Exception(f"opStr {opStr} not found")

    return tree


def constrTreeToENodeExpr(tree, varSet):
    expr = "("
    children = []
    assert isinstance(tree[0], OP)
    children.append(tree[0].name)
    for t in tree[1:]:
        if isinstance(t, list):
            children.append(constrTreeToENodeExpr(t, varSet))
        elif isinstance(t, OP):
            children.append(t.name)
        else:
            children.append("{" + t + "}")
            varSet.add(t)
    expr += " ".join(children)

    expr += ")"
    return expr


def getVar(dependencies, varSet):
    for d in dependencies:
        assert d[-1] == ")"
        split = d[:-1].split("(")
        assert len(split) == 2
        predName, args = split
        vars = args.split(",")
        for v in vars:
            varSet.add(v)


# get return from parseProlog
def buildRust(prologStruct):
    rust = ""
    for predName, rules in prologStruct.items():
        headArgs = rules[0]["headArgs"]

        def headArgsToFnInput(headArgs):
            return ", ".join([f"{arg}: &str" for arg in headArgs])

        def headArgsToSyntax(headArgs):
            return " ".join([f"{{{arg}}}" for arg in headArgs])

        # fn appendDummy(x: &str, y: &str, z: &str) -> String {
        rust += f"fn {predName}Dummy({headArgsToFnInput(headArgs)}) -> String {{\n"
        #     let syntax = format!("(pred <{x} {y} {z}>)");
        rust += f'    let syntax = format!("(pred <{headArgsToSyntax(headArgs)}>)");\n'
        #     format!("(composeInit append {syntax} (true) <2>)")
        rust += f'    format!("(composeInit {predName} {{syntax}} (TODO) <TODO>)")\n'
        # }
        rust += "}\n"
        rust += "\n"

        # fn appendCHC(x: &str, y: &str, z: &str, count: &mut u32, eg: &mut CHCEGraph) -> AppliedId {

        rust += f"fn {predName}CHC({headArgsToFnInput(headArgs)}, count: &mut u32, eg: &mut CHCEGraph) -> AppliedId {{\n"

        #     let syntax = format!("(pred <{x} {y} {z}>)");
        rust += (
            f'    let syntax = format!("(pred <{headArgsToSyntax(headArgs)}>)");\n\n'
        )

        for i, rule in enumerate(rules):
            rust += "    // {}\n".format(rule["line"])
            andChildren = []
            allVar = set()
            for c in rule["constr"]:
                constrTree = parseConstr(c)
                andChildren.append(constrTreeToENodeExpr(constrTree, allVar))

            getVar(rule["dependencies"], allVar)

            for v in allVar - set(headArgs):
                rust += (
                    f"    let {v} = &generateVarFromCount(count, VarType::Unknown);\n"
                )

            #     let cond1 = format!("(and <(eq {x} (emptyList)) (eq {y} {z})>)");
            rust += f'    let cond{i} = format!("(and <{" ".join(andChildren)}>)");\n'

            if len(rule["dependencies"]) == 0:
                rust += f'    let chc{i} = format!("(new {{syntax}} cond{i} <>)");\n'
            else:
                dependencies = rule["dependencies"]
                dependenciesDummy = []
                for d in dependencies:
                    split = d.split("(")
                    assert len(split) == 2
                    predName, args = split
                    dependenciesDummy.append(f"{predName}Dummy({args}")
                rust += f'    let chc{i} = format!("(new {{syntax}} cond{i} <{{}}>)", {", ".join(dependenciesDummy)});\n'

            rust += "\n"

        #     let composeStr = format!("(compose <{chc1} {chc2}>)");
        composeStr = []
        for i in range(len(rules)):
            composeStr.append(f"{{chc{i}}}")
        rust += f'    let composeStr = format!("(compose <{" ".join(composeStr)}>)");\n'
        #     let composeId = eg.addExpr(&composeStr);
        rust += f"    let composeId = eg.addExpr(&composeStr);\n"
        #     let dummyId = eg.addExpr(&appendDummy(x, y, z));
        rust += (
            f"    let dummyId = eg.addExpr(&{predName}Dummy({", ".join(headArgs)}));\n"
        )
        #     eg.union(&composeId, &dummyAppendId);
        rust += f"    eg.union(&composeId, &dummyId);\n"

        rust += "    composeId\n"

        rust += "}\n"
    return rust


# file = open("input.prolog", "r")
# lines = file.readlines()

# separate body but

# Example usage
f = open("prologInp.txt", "r")
lines = f.readlines()
struct = parseProlog(lines)
pprint.pprint(struct)
print(buildRust(struct))

# output

# fn appendDummy(x: &str, y: &str, z: &str) -> String {
#     let syntax = format!("(pred <{x} {y} {z}>)");
#     format!("(composeInit append {syntax} (true) <2>)")
# }
# fn appendCHC(x: &str, y: &str, z: &str, count: &mut u32, eg: &mut CHCEGraph) -> AppliedId {
#     // append(X, Y, Z) :- X = [], Y = Z.
#     // append(X, Y, Z) :- X = [T|X1], Z = [T|Z1], append(X1, Y, Z1).
#     let syntax = format!("(pred <{x} {y} {z}>)");

#     // append(X, Y, Z) :- X = [], Y = Z.
#     let cond1 = format!("(and <(eq {x} (emptyList)) (eq {y} {z})>)");
#     let chc1 = format!("(new {syntax} {cond1} <>)");
#     // append(X, Y, Z) :- X = [T|X1], Z = [T|Z1], append(X1, Y, Z1).
#     let t = &generateVarFromCount(count, VarType::Int);
#     let x1 = &generateVarFromCount(count, VarType::List);
#     let z1 = &generateVarFromCount(count, VarType::List);
#     let cond2 = format!("(and <(eq {x} (list {t} {x1})) (eq {z} (list {t} {z1}))>)");
#     let chc2 = format!("(new {syntax} {cond2} <{}>)", appendDummy(x1, y, z1));

#     let composeAppend = format!("(compose <{chc1} {chc2}>)");
#     let composeAppendId = eg.addExpr(&composeAppend);
#     let dummyAppendId = eg.addExpr(&appendDummy(x, y, z));
#     eg.union(&composeAppendId, &dummyAppendId);

#     composeAppendId
# }
