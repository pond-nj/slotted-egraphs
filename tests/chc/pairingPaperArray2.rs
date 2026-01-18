use std::{cell::RefCell, time::Duration};

use super::*;
use std::thread;

// 32MiB
const STACK_SIZE: usize = 32 * 1024 * 1024;
const ITER_LIMIT: usize = 1;
const TIME_LIMIT_SECS: u64 = 3600;
const DO_CONST_REWRITE: bool = true;

use log::debug;
// append(X, Y, Z) :- X = [], Y = Z.
// append(X, Y, Z) :- X = [T|X1], Z = [T|Z1], append(X1, Y, Z1).

// whl1(A,B,X,Y,A2,B2,X2,Y2) :- A = A2,B = B2,X = X2, Y = Y2, A >= B.
// whl1(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-1, A1=A+1, append(X, [A], X1), append(Y, X, Y1), whl1(A1,B,X1,Y1,A2,B2,X2,Y2).
// ifte(A,B,X,Y,A2,B2,X2,Y2) :- A >= B, A2 = A,B2 = B,X2 = X,Y2 = Y.
// ifte(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-1, LA = [A], append(X, LA, X1), whl2(A,B,X1,Y,A2,B2,X2,Y2).
// whl2(A,B,X,Y,A2,B2,X2,Y2) :- B2 = B,X = X2, A >= B-1, A2=A+1, append(Y, X, Y2).
// whl2(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-2, A1 = A + 1, append(X, [A1], X1), append(Y, X, Y1), whl2(A1,B,X1,Y1,A2,B2,X2,Y2).

// sum_list(X, Y) :- X = [], Y = 0.
// sum_list(X, Y) :- X = [H|T], Y = S, sum_list(T, S1), S = H + S1.
fn appendDummy(new_0: &str, new_1: &str, new_2: &str) -> String {
    let syntax = format!("(pred <{new_0} {new_1} {new_2}>)");
    format!("(composeInit append {syntax} (TODO) <TODO>)")
}

fn appendCHC(
    new_0: &str,
    new_1: &str,
    new_2: &str,
    count: &mut u32,
    eg: &mut CHCEGraph,
) -> AppliedId {
    let syntax = format!("(pred <{new_0} {new_1} {new_2}>)");

    let syntaxAppId = eg.addExpr(&syntax);
    // append([], X, X)
    let X = &generateVarFromCount(count, VarType::Unknown);
    let cond0 = format!("(and <(eq (emptyList) {new_0}) (eq {X} {new_2})>)");
    let chc0 = format!("(new {syntax} {cond0} <>)");
    let chc0AppId = eg.addExpr(&chc0);
    eg.shrink_slots(&chc0AppId, &syntaxAppId.slots(), ());

    // append([T|X], Y, [T|Z]) :- append(X, Y, Z)
    let X = &generateVarFromCount(count, VarType::Unknown);
    let T = &generateVarFromCount(count, VarType::Unknown);
    let Z = &generateVarFromCount(count, VarType::Unknown);
    let Y = &generateVarFromCount(count, VarType::Unknown);
    let cond1 = format!("(and <(list {T} {X}) (eq {Y} {new_1}) (list {T} {Z})>)");
    let chc1 = format!("(new {syntax} {cond1} <{}>)", appendDummy(X, new_1, Z));
    let chc1AppId = eg.addExpr(&chc1);
    eg.shrink_slots(&chc1AppId, &syntaxAppId.slots(), ());

    let composeStr = format!("(compose <{chc0} {chc1}>)");
    let composeId = eg.addExpr(&composeStr);
    let dummyId = eg.addExpr(&appendDummy(new_0, new_1, new_2));
    eg.union(&composeId, &dummyId);
    composeId
}

fn whl1Dummy(
    new_0: &str,
    new_1: &str,
    new_2: &str,
    new_3: &str,
    new_4: &str,
    new_5: &str,
    new_6: &str,
    new_7: &str,
) -> String {
    let syntax =
        format!("(pred <{new_0} {new_1} {new_2} {new_3} {new_4} {new_5} {new_6} {new_7}>)");
    format!("(composeInit whl1 {syntax} (TODO) <TODO>)")
}

fn whl1CHC(
    new_0: &str,
    new_1: &str,
    new_2: &str,
    new_3: &str,
    new_4: &str,
    new_5: &str,
    new_6: &str,
    new_7: &str,
    count: &mut u32,
    eg: &mut CHCEGraph,
) -> AppliedId {
    let syntax =
        format!("(pred <{new_0} {new_1} {new_2} {new_3} {new_4} {new_5} {new_6} {new_7}>)");

    let syntaxAppId = eg.addExpr(&syntax);
    // whl1(A,B,X,Y,A,B,X,Y) :- A >= B
    let X = &generateVarFromCount(count, VarType::Unknown);
    let A = &generateVarFromCount(count, VarType::Unknown);
    let B = &generateVarFromCount(count, VarType::Unknown);
    let Y = &generateVarFromCount(count, VarType::Unknown);
    let cond0 = format!(
        "(and <(eq {A} {new_4}) (eq {B} {new_5}) (eq {X} {new_6}) (eq {Y} {new_7}) (geq {A} {B})>)"
    );
    let chc0 = format!("(new {syntax} {cond0} <>)");
    let chc0AppId = eg.addExpr(&chc0);
    eg.shrink_slots(&chc0AppId, &syntaxAppId.slots(), ());

    // whl1(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-1, A1=A+1, append(X, [A], X1), append(Y, X, Y1), whl1(A1,B,X1,Y1,A2,B2,X2,Y2)
    let new_8 = &generateVarFromCount(count, VarType::Unknown);
    let A2 = &generateVarFromCount(count, VarType::Unknown);
    let Y = &generateVarFromCount(count, VarType::Unknown);
    let Y2 = &generateVarFromCount(count, VarType::Unknown);
    let X2 = &generateVarFromCount(count, VarType::Unknown);
    let X1 = &generateVarFromCount(count, VarType::Unknown);
    let X = &generateVarFromCount(count, VarType::Unknown);
    let A = &generateVarFromCount(count, VarType::Unknown);
    let B2 = &generateVarFromCount(count, VarType::Unknown);
    let A1 = &generateVarFromCount(count, VarType::Unknown);
    let Y1 = &generateVarFromCount(count, VarType::Unknown);
    let B = &generateVarFromCount(count, VarType::Unknown);
    let cond1 = format!("(and <(eq {A} {new_0}) (eq {B} {new_1}) (eq {X} {new_2}) (eq {Y} {new_3}) (eq {A2} {new_4}) (eq {B2} {new_5}) (eq {X2} {new_6}) (eq {Y2} {new_7}) (list {A} (emptyList)) (leq {A} (minus {B} 1)) (eq {A1} (add {A} 1))>)");
    let chc1 = format!(
        "(new {syntax} {cond1} <{} {} {}>)",
        appendDummy(new_2, new_8, X1),
        appendDummy(new_3, new_2, Y1),
        whl1Dummy(A1, new_1, X1, Y1, new_4, new_5, new_6, new_7)
    );
    let chc1AppId = eg.addExpr(&chc1);
    eg.shrink_slots(&chc1AppId, &syntaxAppId.slots(), ());

    let composeStr = format!("(compose <{chc0} {chc1}>)");
    let composeId = eg.addExpr(&composeStr);
    let dummyId = eg.addExpr(&whl1Dummy(
        new_0, new_1, new_2, new_3, new_4, new_5, new_6, new_7,
    ));
    eg.union(&composeId, &dummyId);
    composeId
}

fn ifteDummy(
    new_0: &str,
    new_1: &str,
    new_2: &str,
    new_3: &str,
    new_4: &str,
    new_5: &str,
    new_6: &str,
    new_7: &str,
) -> String {
    let syntax =
        format!("(pred <{new_0} {new_1} {new_2} {new_3} {new_4} {new_5} {new_6} {new_7}>)");
    format!("(composeInit ifte {syntax} (TODO) <TODO>)")
}

fn ifteCHC(
    new_0: &str,
    new_1: &str,
    new_2: &str,
    new_3: &str,
    new_4: &str,
    new_5: &str,
    new_6: &str,
    new_7: &str,
    count: &mut u32,
    eg: &mut CHCEGraph,
) -> AppliedId {
    let syntax =
        format!("(pred <{new_0} {new_1} {new_2} {new_3} {new_4} {new_5} {new_6} {new_7}>)");

    let syntaxAppId = eg.addExpr(&syntax);
    // ifte(A,B,X,Y,A,B,X,Y ) :- A >= B
    let X = &generateVarFromCount(count, VarType::Unknown);
    let A = &generateVarFromCount(count, VarType::Unknown);
    let B = &generateVarFromCount(count, VarType::Unknown);
    let Y = &generateVarFromCount(count, VarType::Unknown);
    let cond0 = format!(
        "(and <(eq {A} {new_4}) (eq {B} {new_5}) (eq {X} {new_6}) (eq {Y} {new_7}) (geq {A} {B})>)"
    );
    let chc0 = format!("(new {syntax} {cond0} <>)");
    let chc0AppId = eg.addExpr(&chc0);
    eg.shrink_slots(&chc0AppId, &syntaxAppId.slots(), ());

    // ifte(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-1,    append(X, [A], X1), whl2(A,B,X1,Y,A2,B2,X2,Y2)
    let new_8 = &generateVarFromCount(count, VarType::Unknown);
    let A2 = &generateVarFromCount(count, VarType::Unknown);
    let Y2 = &generateVarFromCount(count, VarType::Unknown);
    let Y = &generateVarFromCount(count, VarType::Unknown);
    let X2 = &generateVarFromCount(count, VarType::Unknown);
    let X1 = &generateVarFromCount(count, VarType::Unknown);
    let X = &generateVarFromCount(count, VarType::Unknown);
    let A = &generateVarFromCount(count, VarType::Unknown);
    let B2 = &generateVarFromCount(count, VarType::Unknown);
    let B = &generateVarFromCount(count, VarType::Unknown);
    let cond1 = format!("(and <(eq {A} {new_0}) (eq {B} {new_1}) (eq {X} {new_2}) (eq {Y} {new_3}) (eq {A2} {new_4}) (eq {B2} {new_5}) (eq {X2} {new_6}) (eq {Y2} {new_7}) (list {A} (emptyList)) (leq {A} (minus {B} 1))>)");
    let chc1 = format!(
        "(new {syntax} {cond1} <{} {}>)",
        appendDummy(new_2, new_8, X1),
        whl2Dummy(new_0, new_1, X1, new_3, new_4, new_5, new_6, new_7)
    );
    let chc1AppId = eg.addExpr(&chc1);
    eg.shrink_slots(&chc1AppId, &syntaxAppId.slots(), ());

    let composeStr = format!("(compose <{chc0} {chc1}>)");
    let composeId = eg.addExpr(&composeStr);
    let dummyId = eg.addExpr(&ifteDummy(
        new_0, new_1, new_2, new_3, new_4, new_5, new_6, new_7,
    ));
    eg.union(&composeId, &dummyId);
    composeId
}

fn whl2Dummy(
    new_0: &str,
    new_1: &str,
    new_2: &str,
    new_3: &str,
    new_4: &str,
    new_5: &str,
    new_6: &str,
    new_7: &str,
) -> String {
    let syntax =
        format!("(pred <{new_0} {new_1} {new_2} {new_3} {new_4} {new_5} {new_6} {new_7}>)");
    format!("(composeInit whl2 {syntax} (TODO) <TODO>)")
}

fn whl2CHC(
    new_0: &str,
    new_1: &str,
    new_2: &str,
    new_3: &str,
    new_4: &str,
    new_5: &str,
    new_6: &str,
    new_7: &str,
    count: &mut u32,
    eg: &mut CHCEGraph,
) -> AppliedId {
    let syntax =
        format!("(pred <{new_0} {new_1} {new_2} {new_3} {new_4} {new_5} {new_6} {new_7}>)");

    let syntaxAppId = eg.addExpr(&syntax);
    // whl2(A,B,X,Y,A2,B,X,Y2) :- A >= B-1, A2=A+1,    append(Y, X, Y2)
    let A2 = &generateVarFromCount(count, VarType::Unknown);
    let Y2 = &generateVarFromCount(count, VarType::Unknown);
    let Y = &generateVarFromCount(count, VarType::Unknown);
    let X = &generateVarFromCount(count, VarType::Unknown);
    let A = &generateVarFromCount(count, VarType::Unknown);
    let B = &generateVarFromCount(count, VarType::Unknown);
    let cond0 = format!("(and <(eq {A} {new_0}) (eq {B} {new_5}) (eq {X} {new_6}) (eq {Y} {new_3}) (eq {A2} {new_4}) (eq {Y2} {new_7}) (geq {A} (minus {B} 1)) (eq {A2} (add {A} 1))>)");
    let chc0 = format!(
        "(new {syntax} {cond0} <{}>)",
        appendDummy(new_3, new_6, new_7)
    );
    let chc0AppId = eg.addExpr(&chc0);
    eg.shrink_slots(&chc0AppId, &syntaxAppId.slots(), ());

    // whl2(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-2,    A1 = A + 1,    append(X, [A1], X1),    append(Y, X, Y1),    whl2(A1,B,X1,Y1,A2,B2,X2,Y2)
    let new_8 = &generateVarFromCount(count, VarType::Unknown);
    let A2 = &generateVarFromCount(count, VarType::Unknown);
    let Y = &generateVarFromCount(count, VarType::Unknown);
    let Y2 = &generateVarFromCount(count, VarType::Unknown);
    let X2 = &generateVarFromCount(count, VarType::Unknown);
    let X1 = &generateVarFromCount(count, VarType::Unknown);
    let X = &generateVarFromCount(count, VarType::Unknown);
    let A = &generateVarFromCount(count, VarType::Unknown);
    let B2 = &generateVarFromCount(count, VarType::Unknown);
    let A1 = &generateVarFromCount(count, VarType::Unknown);
    let Y1 = &generateVarFromCount(count, VarType::Unknown);
    let B = &generateVarFromCount(count, VarType::Unknown);
    let cond1 = format!("(and <(eq {A} {new_0}) (eq {B} {new_1}) (eq {X} {new_2}) (eq {Y} {new_3}) (eq {A2} {new_4}) (eq {B2} {new_5}) (eq {X2} {new_6}) (eq {Y2} {new_7}) (list {A1} (emptyList)) (leq {A} (minus {B} 2)) (eq {A1} (add {A} 1))>)");
    let chc1 = format!(
        "(new {syntax} {cond1} <{} {} {}>)",
        appendDummy(new_2, new_8, X1),
        appendDummy(new_3, new_2, Y1),
        whl2Dummy(A1, new_1, X1, Y1, new_4, new_5, new_6, new_7)
    );
    let chc1AppId = eg.addExpr(&chc1);
    eg.shrink_slots(&chc1AppId, &syntaxAppId.slots(), ());

    let composeStr = format!("(compose <{chc0} {chc1}>)");
    let composeId = eg.addExpr(&composeStr);
    let dummyId = eg.addExpr(&whl2Dummy(
        new_0, new_1, new_2, new_3, new_4, new_5, new_6, new_7,
    ));
    eg.union(&composeId, &dummyId);
    composeId
}

fn sum_listDummy(new_0: &str, new_1: &str) -> String {
    let syntax = format!("(pred <{new_0} {new_1}>)");
    format!("(composeInit sum_list {syntax} (TODO) <TODO>)")
}

fn sum_listCHC(new_0: &str, new_1: &str, count: &mut u32, eg: &mut CHCEGraph) -> AppliedId {
    let syntax = format!("(pred <{new_0} {new_1}>)");

    let syntaxAppId = eg.addExpr(&syntax);
    // sum_list([], 0)
    let cond0 = format!("(and <(eq (emptyList) {new_0}) (eq 0 {new_1})>)");
    let chc0 = format!("(new {syntax} {cond0} <>)");
    let chc0AppId = eg.addExpr(&chc0);
    eg.shrink_slots(&chc0AppId, &syntaxAppId.slots(), ());

    // sum_list([H|T], S) :- sum_list(T, S1), S = H + S1
    let S = &generateVarFromCount(count, VarType::Unknown);
    let T = &generateVarFromCount(count, VarType::Unknown);
    let S1 = &generateVarFromCount(count, VarType::Unknown);
    let H = &generateVarFromCount(count, VarType::Unknown);
    let cond1 = format!("(and <(list {H} {T}) (eq {S} {new_1}) (eq {S} (add {H} {S1}))>)");
    let chc1 = format!("(new {syntax} {cond1} <{}>)", sum_listDummy(T, S1));
    let chc1AppId = eg.addExpr(&chc1);
    eg.shrink_slots(&chc1AppId, &syntaxAppId.slots(), ());

    let composeStr = format!("(compose <{chc0} {chc1}>)");
    let composeId = eg.addExpr(&composeStr);
    let dummyId = eg.addExpr(&sum_listDummy(new_0, new_1));
    eg.union(&composeId, &dummyId);
    composeId
}

fn incorrectDummy() -> String {
    let syntax = format!("(pred <>)");
    format!("(composeInit incorrect {syntax} (TODO) <TODO>)")
}

fn incorrectCHC(count: &mut u32, eg: &mut CHCEGraph) -> AppliedId {
    let syntax = format!("(pred <>)");

    let syntaxAppId = eg.addExpr(&syntax);
    // incorrect :- N1 =\= N2, sum_list(X1, N1), sum_list(X2, N2), whl1(A,B,X,Y,A1,B1,X1,Y1), ifte(A, B,X,Y,A2,B2,X2,Y2)
    let N1 = &generateVarFromCount(count, VarType::Unknown);
    let Y = &generateVarFromCount(count, VarType::Unknown);
    let A2 = &generateVarFromCount(count, VarType::Unknown);
    let Y2 = &generateVarFromCount(count, VarType::Unknown);
    let X2 = &generateVarFromCount(count, VarType::Unknown);
    let X1 = &generateVarFromCount(count, VarType::Unknown);
    let X = &generateVarFromCount(count, VarType::Unknown);
    let B1 = &generateVarFromCount(count, VarType::Unknown);
    let A = &generateVarFromCount(count, VarType::Unknown);
    let N2 = &generateVarFromCount(count, VarType::Unknown);
    let A1 = &generateVarFromCount(count, VarType::Unknown);
    let B2 = &generateVarFromCount(count, VarType::Unknown);
    let Y1 = &generateVarFromCount(count, VarType::Unknown);
    let B = &generateVarFromCount(count, VarType::Unknown);
    let cond0 = format!("(and <(neq {N1} {N2})>)");
    let chc0 = format!(
        "(new {syntax} {cond0} <{} {} {} {}>)",
        sum_listDummy(X1, N1),
        sum_listDummy(X2, N2),
        whl1Dummy(A, B, X, Y, A1, B1, X1, Y1),
        ifteDummy(A, B, X, Y, A2, B2, X2, Y2)
    );
    let chc0AppId = eg.addExpr(&chc0);
    eg.shrink_slots(&chc0AppId, &syntaxAppId.slots(), ());

    let composeStr = format!("(compose <{chc0}>)");
    let composeId = eg.addExpr(&composeStr);
    let dummyId = eg.addExpr(&incorrectDummy());
    eg.union(&composeId, &dummyId);
    composeId
}
