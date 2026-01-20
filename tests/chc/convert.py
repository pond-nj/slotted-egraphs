# input
# append(X, Y, Z) :- X = [], Y = Z.
# append(X, Y, Z) :- X = [T|X1], Z = [T|Z1], append(X1, Y, Z1).

from collections import defaultdict
from enum import Enum
import pprint
import re
import unionfind


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
    metadata = {
        "headType": {},
        "functional": {},
    }
    headType = metadata["headType"]
    functional = metadata["functional"]

    for line in lines:
        rule = {}
        changeVar = {}
        line = line.strip()
        if line.startswith("%"):
            continue

        if line.startswith("#t"):
            print("line", line)
            res = re.match(r"^#t\s*(\w*)\((.*)\) (true|false) <(.*)>.$", line)
            assert res
            predName = res.group(1)
            if res.group(2) == "":
                headType[predName] = []
            else:
                types = res.group(2).split(",")
                for i in range(len(types)):
                    types[i] = types[i].strip()
                    assert types[i] in ["int", "node", "list"]
                headType[predName] = types

            functional[predName] = {
                "isTrue": res.group(3) == "true",
                "idx": res.group(4).split(),
            }

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
        assert headPred in headType
        if "(" in head:
            assert re.match(r"^(\w*)\((.*)\)$", head)
            headArgs = list(
                map(lambda x: x.strip(), head.split("(")[1].split(")")[0].split(","))
            )
        else:
            headArgs = []
        assert len(headArgs) == len(headType[headPred])

        constr = []
        newHeadArgs = []
        changeVar = {}

        for i, h in enumerate(headArgs):
            newHeadArgs.append(f"new_{i}")
            changeVar[h] = f"new_{i}"

        body = parseBody(body)

        dependencies = []
        for b in body:
            b = b.strip()
            res = re.match(r"^(\w*)\((.*)\)$", b)
            if res:
                bPred = res.group(1)
                bArgs = res.group(2).split(",")
                for i, v in enumerate(bArgs):
                    v = v.strip()
                    if v in changeVar:
                        bArgs[i] = changeVar[v]
                        continue

                    if not re.match(r"^\w+$", v) and not v in changeVar:
                        changeVar[v] = "new_" + str(len(changeVar))
                        bArgs[i] = changeVar[v]

                dependencies.append(bPred + "(" + ", ".join(bArgs) + ")")
            else:
                constr.append(b)

        newConstr = []
        for v in changeVar:
            newConstr.append(f"{v} = {changeVar[v]}")
        newConstr.extend(constr)

        rule = {
            "headArgs": newHeadArgs,
            "constr": newConstr,
            "dependencies": dependencies,
            "line": line,
        }
        ret[headPred].append(rule)
    return (
        ret,
        metadata,
    )


class OP(Enum):
    eq = "="
    neq = "=\\="
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


def unwrapParse(t):
    res = parseConstr(t)
    if len(res) == 1:
        return res[0]

    return res


def parseConstr(constr):
    origConstr = constr
    constr = constr.strip()
    tree = []

    if constr == "":
        print(f"parseConstr {origConstr} -> []")
        return []

    if constr.isnumeric():
        print(f"parseConstr {origConstr} -> [{int(constr)}]")
        return [int(constr)]

    if re.match(r"^\w+$", constr):
        print(f"parseConstr {origConstr} -> [{constr}]")
        return [constr]

    if constr == "[]":
        print(f"parseConstr {origConstr} -> [{OP.emptyList}]")
        return [OP.emptyList]

    if constr[0] == "[" and constr[-1] == "]":
        constr = constr[1:-1]
        if "|" in constr:
            assert constr.count("|") == 1
            left, right = constr.split("|")
            print(
                f"parseConstr {origConstr} -> [{OP.list}, {unwrapParse(left)}, {unwrapParse(right)}]"
            )
            return [OP.list, unwrapParse(left), unwrapParse(right)]
        else:
            assert re.match(r"^\w+$", constr)
            print(
                f"parseConstr {origConstr} -> [{OP.list}, {unwrapParse(constr)}, {OP.emptyList}]"
            )
            return [OP.list, unwrapParse(constr), OP.emptyList]

    res = re.match(r"^node\((.*)\)$", constr)
    if res:
        print("match found")
        args = res.group(1).split(",")
        assert len(args) == 3
        print(
            f"parseConstr {origConstr} -> [{OP.binode}, {unwrapParse(args[0])}, {unwrapParse(args[1])}, {unwrapParse(args[2])}]"
        )
        return [
            OP.binode,
            unwrapParse(args[0]),
            unwrapParse(args[1]),
            unwrapParse(args[2]),
        ]

    first, constr = constrGetNextTerm(constr)
    opStr, constr = constrGetNextTerm(constr)
    try:
        op = OP(opStr)
        tree.append(op)
        tree.append(unwrapParse(first))
        tree.append(unwrapParse(constr))
    except KeyError:
        raise Exception(f"opStr {opStr} not found")

    print(f"parseConstr {origConstr} -> {tree}")
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
            children.append("(" + t.name + ")")
        elif isinstance(t, int):
            children.append(str(t))
        else:
            children.append("{" + t + "}")
            varSet.add(t)
    expr += " ".join(children)

    expr += ")"
    print(f"constrTreeToENodeExpr {tree} -> {expr}")
    return expr


def getVar(dependencies, varSet):
    for d in dependencies:
        assert d[-1] == ")"
        split = d[:-1].split("(")
        assert len(split) == 2
        predName, args = split
        vars = args.split(",")
        for v in vars:
            v = v.strip()
            varSet.add(v)


# get return from parseProlog
def buildRust(lines, prologStruct, metadata):
    headType = metadata["headType"]
    functional = metadata["functional"]

    rust = ""
    for line in lines:
        rust += "// " + line
    rust += "\n"

    rust += """
use std::{cell::RefCell, time::Duration};

use super::*;
use std::thread;

// 32MiB
const STACK_SIZE: usize = 32 * 1024 * 1024;
const ITER_LIMIT: usize = 1;
const TIME_LIMIT_SECS: u64 = 3600;
const DO_CONST_REWRITE: bool = true;

use log::debug;

"""
    for predName, rules in prologStruct.items():
        headArgs = rules[0]["headArgs"]

        def headArgsToFnInput(headArgs):
            return [f"{arg}: &str" for arg in headArgs]

        def headArgsToSyntax(headArgs):
            return " ".join([f"{{{arg}}}" for arg in headArgs])

        # fn appendDummy(x: &str, y: &str, z: &str) -> String {
        rust += f"fn {predName}Dummy({", ".join(headArgsToFnInput(headArgs))}) -> String {{\n"
        #     let syntax = format!("(pred <{x} {y} {z}>)");
        rust += f'    let syntax = format!("(pred <{headArgsToSyntax(headArgs)}>)");\n'
        #     format!("(composeInit append {syntax} (true) <2>)")
        rust += f'    format!("(composeInit {predName} {{syntax}} ({str(functional[predName]["isTrue"]).lower()}) <{" ".join(functional[predName]["idx"])}>)")\n'
        # }
        rust += "}\n"
        rust += "\n"

        # fn appendCHC(x: &str, y: &str, z: &str, count: &mut u32, eg: &mut CHCEGraph) -> AppliedId {
        fnInput = headArgsToFnInput(headArgs)
        fnInput.append("count: &mut u32")
        fnInput.append("eg: &mut CHCEGraph")
        rust += f"fn {predName}CHC({", ".join(fnInput)}) -> AppliedId {{\n"

        #     let syntax = format!("(pred <{x} {y} {z}>)");
        rust += (
            f'    let syntax = format!("(pred <{headArgsToSyntax(headArgs)}>)");\n\n'
        )
        #     let syntaxAppId = eg.addExpr(&syntax);
        rust += f"    let syntaxAppId = eg.addExpr(&syntax);\n"

        for i, rule in enumerate(rules):
            rust += "    // {}\n".format(rule["line"])
            andChildren = []
            allVar = set()
            uf = unionfind.UnionFind()
            m = {}
            type = {}
            for c in rule["constr"]:
                constrTree = parseConstr(c)
                res = re.match(r"^(\w+)\s*=\s*(\w+)$", c)
                if res:
                    l = res.group(1)
                    r = res.group(2)
                    if not l in m:
                        m[l] = len(m)
                        uf.extend()
                        assert uf.find(m[l]) == m[l]
                    if not r in m:
                        m[r] = len(m)
                        uf.extend()
                        assert uf.find(m[r]) == m[r]
                    uf.union(m[l], m[r])
                andChildren.append(constrTreeToENodeExpr(constrTree, allVar))

            for d in rule["dependencies"]:
                res = re.match(r"^(\w+)\((.*)\)$", d)
                assert res
                dPredName = res.group(1)
                args = res.group(2).split(",")

                assert len(args) == len(headType[dPredName])

                for j, v in enumerate(args):
                    v = v.strip()
                    type[v] = headType[dPredName][j]

            pprint.pprint(rule)
            pprint.pprint(f"line {rule['line']}")
            pprint.pprint(f"type {type}")

            groups = defaultdict(list)
            for v in m:
                groups[uf.find(m[v])].append(v)

            for group in groups.values():
                for v in group:
                    if v in headArgs:
                        for t in group:
                            type[t] = headType[predName][headArgs.index(v)]
                        break

            assert not "[]" in allVar

            getVar(rule["dependencies"], allVar)

            for v in allVar - set(headArgs):
                if v in type:
                    rust += f"    let {v} = &generateVarFromCount(count, VarType::{type[v].capitalize()});\n"
                else:
                    rust += f"    let {v} = &generateVarFromCount(count, VarType::Unknown);\n"

            #     let cond1 = format!("(and <(eq {x} (emptyList)) (eq {y} {z})>)");
            rust += f'    let cond{i} = format!("(and <{" ".join(andChildren)}>)");\n'

            if len(rule["dependencies"]) == 0:
                rust += (
                    f'    let chc{i} = format!("(new {{syntax}} {{cond{i}}} <>)");\n'
                )
            else:
                dependencies = rule["dependencies"]
                dependenciesDummy = []
                for d in dependencies:
                    split = d.split("(")
                    assert len(split) == 2
                    dPredName, args = split
                    dependenciesDummy.append(f"{dPredName}Dummy({args}")

                rust += f'    let chc{i} = format!("(new {{syntax}} {{cond{i}}} <{" ".join(["{}" for _ in dependenciesDummy])}>)", {", ".join(dependenciesDummy)});\n'

            #     let chc1AppId = eg.addExpr(&chc1);
            rust += f"    let chc{i}AppId = eg.addExpr(&chc{i});\n"
            #     eg.shrink_slots(&chc1AppId, &syntaxAppId.slots(), ());
            rust += f"    eg.shrink_slots(&eg.find_applied_id(&chc{i}AppId), &syntaxAppId.slots(), ());\n"

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

        rust += "}\n\n"

    # fn buildCHC(mut eg: CHCEGraph, count: &mut u32) -> (AppliedId, CHCRunner) {
    rust += (
        "fn buildCHC(mut eg: CHCEGraph, count: &mut u32) -> (AppliedId, CHCRunner) {\n"
    )
    #     let n = &generateVarFromCount(count, VarType::Int);
    #     let t = &generateVarFromCount(count, VarType::Node);
    #     let u = &generateVarFromCount(count, VarType::Node);
    #     let m = &generateVarFromCount(count, VarType::Int);
    #     let k = &generateVarFromCount(count, VarType::Int);

    for predName, rules in prologStruct.items():
        for i, v in enumerate(rules[0]["headArgs"]):
            rust += f"    let {v} = &generateVarFromCount(count, VarType::{headType[predName][i].capitalize()});\n"

        #     let rootDummyId = eg.addExpr(&rootDummy(n, t, u, m, k));
        rust += f'    let {predName}DummyId = eg.addExpr(&{predName}Dummy({", ".join(rules[0]["headArgs"])}));\n'

        #     let rootId = rootCHC(n, m, k, t, u, &mut eg);
        inp = rules[0]["headArgs"]
        inp.append("count")
        inp.append("&mut eg")
        rust += f'    let {predName}Id = {predName}CHC({", ".join(inp)});\n'
        #     eg.union(&rootId, &rootDummyId);
        rust += f"    eg.union(&{predName}Id, &{predName}DummyId);\n\n"

    rust += "dumpCHCEGraph(&eg);\n"

    rust += """
    let mut runner: CHCRunner = Runner::default()
        .with_egraph(eg)
        .with_iter_limit(ITER_LIMIT)
        .with_time_limit(Duration::from_secs(TIME_LIMIT_SECS));
    let (report, t): (Report, _) = time(|| {
        runner.run(&mut getAllRewrites(
            RewriteList::default(),
            DO_CONST_REWRITE,
        ))
    });\n
    """
    rust += '    println!("use time {t:?}");\n'
    rust += '    println!("report {report:?}");\n\n'

    rust += '    println!("egraph after run");\n'
    rust += "    dumpCHCEGraph(&runner.egraph);\n"

    rust += "    runner.egraph.check();\n"

    rust += "    (incorrectId, runner)\n"
    # }
    rust += "}\n\n"

    rust += """
fn mainTestSpawn() {
    initLogger();
    let mut egOrig = CHCEGraph::default();
    let mut count = 0;
    let doConstraintRewrite = true;
    let (rootId, mut runner) = buildCHC(egOrig, &mut count);
    checkSelfCycle(&runner.egraph);
}

#[test]
fn mainTest() {
    let child = thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(mainTestSpawn)
        .expect("Failed to spawn thread");

    // Wait for the thread to finish
    child.join().expect("Thread panicked");
}
"""

    return rust


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


fname = "prologInp.txt"
f = open(fname, "r")
lines = f.readlines()
newLines = groupLines(lines)
struct, metadata = parseProlog(newLines)
pprint.pprint(struct)
rust = buildRust(lines, struct, metadata)
with open(f"{fname}_rust", "w") as f:
    f.write(rust)

# output

# fn appendDummy(x: &str, y: &str, z: &str) -> String {
#     let syntax = format!("(pred <{x} {y} {z}>)");
#     format!("(composeInit append {syntax} (true) <2>)")
# }
# fn appendCHC(x: &str, y: &str, z: &str, count: &mut u32, eg: &mut CHCEGraph) -> AppliedId {
#     // append(X, Y, Z) :- X = [], Y = Z.
#     // append(X, Y, Z) :- X = [T|X1], Z = [T|Z1], append(X1, Y, Z1).
#     let syntax = format!("(pred <{x} {y} {z}>)");
#     let syntaxAppId = eg.addExpr(&syntax);

#     // append(X, Y, Z) :- X = [], Y = Z.
#     let cond1 = format!("(and <(eq {x} (emptyList)) (eq {y} {z})>)");
#     let chc1 = format!("(new {syntax} {cond1} <>)");
#     let chc1AppId = eg.addExpr(&chc1);
#     eg.shrink_slots(&chc1AppId, &syntaxAppId.slots(), ());

#     // append(X, Y, Z) :- X = [T|X1], Z = [T|Z1], append(X1, Y, Z1).
#     let t = &generateVarFromCount(count, VarType::Int);
#     let x1 = &generateVarFromCount(count, VarType::List);
#     let z1 = &generateVarFromCount(count, VarType::List);
#     let cond2 = format!("(and <(eq {x} (list {t} {x1})) (eq {z} (list {t} {z1}))>)");
#     let chc2 = format!("(new {syntax} {cond2} <{}>)", appendDummy(x1, y, z1));
#     let chc2AppId = eg.addExpr(&chc2);
#     eg.shrink_slots(&chc2AppId, &syntaxAppId.slots(), ());

#     let composeAppend = format!("(compose <{chc1} {chc2}>)");
#     let composeAppendId = eg.addExpr(&composeAppend);
#     let dummyAppendId = eg.addExpr(&appendDummy(x, y, z));
#     eg.union(&composeAppendId, &dummyAppendId);

#     composeAppendId
# }
