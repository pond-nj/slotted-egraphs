# input
# append(X, Y, Z) :- X = [], Y = Z.
# append(X, Y, Z) :- X = [T|X1], Z = [T|Z1], append(X1, Y, Z1).

from collections import defaultdict
from enum import Enum
import pprint
import re
from prologToAST import groupLines, parseProlog
from ast import ConstrOP
import unionfind as unionfind


def constrTreeToENodeExpr(tree, varSet):
    expr = "("
    children = []
    assert isinstance(tree[0], ConstrOP)
    children.append(tree[0].name)
    for t in tree[1:]:
        if isinstance(t, list):
            children.append(constrTreeToENodeExpr(t, varSet))
        elif isinstance(t, ConstrOP):
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
