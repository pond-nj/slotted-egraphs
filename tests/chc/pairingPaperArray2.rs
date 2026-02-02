// #t append(list, list, list) true <2>.
// append([], X, X).
// append([T|X], Y, [T|Z]) :- append(X, Y, Z).
//
// #t whl1(int, int, list, list, int, int, list, list) true <4 5 6 7>.
// whl1(A,B,X,Y,A,B,X,Y) :- A >= B.
// whl1(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-1, A1=A+1, append(X, [A], X1), append(Y, X, Y1), whl1(A1,B,X1,Y1,A2,B2,X2,Y2).
//
// #t ifte(int, int, list, list, int, int, list, list) true <4 5 6 7>.
// ifte(A,B,X,Y,A,B,X,Y ) :- A >= B.
// ifte(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-1,
//     append(X, [A], X1), whl2(A,B,X1,Y,A2,B2,X2,Y2).
//
// #t whl2(int, int, list, list, int, int, list, list) true <4 5 6 7>.
// whl2(A,B,X,Y,A2,B,X,Y2) :- A >= B-1, A2=A+1,
//     append(Y, X, Y2).
// whl2(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-2,
//     A1 = A + 1,
//     append(X, [A1], X1),
//     append(Y, X, Y1),
//     whl2(A1,B,X1,Y1,A2,B2,X2,Y2).
//
// #t sum_list(list, int) true <1>.
// sum_list([], 0).
// sum_list([H|T], S) :- sum_list(T, S1), S = H + S1.
//
// #t incorrect() false <>.
// incorrect :- N1 =\= N2, sum_list(X1, N1), sum_list(X2, N2), whl1(A,B,X,Y,A1,B1,X1,Y1), ifte(A, B,X,Y,A2,B2,X2,Y2).
//

use std::{cell::RefCell, time::Duration};

use super::*;
use std::thread;

// 32MiB
const STACK_SIZE: usize = 32 * 1024 * 1024;
const ITER_LIMIT: usize = 3;
const TIME_LIMIT_SECS: u64 = 3600;
const DO_CONST_REWRITE: bool = true;
const DO_FOLDING: bool = true;

use log::debug;

fn appendDummy(new_0: &str, new_1: &str, new_2: &str) -> String {
    let syntax = format!("(pred <{new_0} {new_1} {new_2}>)");
    format!("(composeInit append {syntax} (true) <2>)")
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
    let X = &generateVarFromCount(count, VarType::List);
    let cond0 = format!("(and <(eq (emptyList) {new_0}) (eq {X} {new_2})>)");
    let chc0 = format!("(new {syntax} {cond0} <>)");
    let chc0AppId = eg.addExpr(&chc0);
    eg.shrink_slots(&eg.find_applied_id(&chc0AppId), &syntaxAppId.slots(), ());

    // append([T|X], Y, [T|Z]) :- append(X, Y, Z)
    let X = &generateVarFromCount(count, VarType::List);
    let Y = &generateVarFromCount(count, VarType::List);
    let T = &generateVarFromCount(count, VarType::Int);
    let Z = &generateVarFromCount(count, VarType::List);
    let cond1 =
        format!("(and <(eq (list {T} {X}) {new_0}) (eq {Y} {new_1}) (eq (list {T} {Z}) {new_2})>)");
    let chc1 = format!("(new {syntax} {cond1} <{}>)", appendDummy(X, new_1, Z));
    let chc1AppId = eg.addExpr(&chc1);
    eg.shrink_slots(&eg.find_applied_id(&chc1AppId), &syntaxAppId.slots(), ());

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
    format!("(composeInit whl1 {syntax} (true) <4 5 6 7>)")
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
    let X = &generateVarFromCount(count, VarType::List);
    let A = &generateVarFromCount(count, VarType::Int);
    let Y = &generateVarFromCount(count, VarType::List);
    let B = &generateVarFromCount(count, VarType::Int);
    let cond0 = format!(
        "(and <(eq {A} {new_4}) (eq {B} {new_5}) (eq {X} {new_6}) (eq {Y} {new_7}) (geq {A} {B})>)"
    );
    let chc0 = format!("(new {syntax} {cond0} <>)");
    let chc0AppId = eg.addExpr(&chc0);
    eg.shrink_slots(&eg.find_applied_id(&chc0AppId), &syntaxAppId.slots(), ());

    // whl1(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-1, A1=A+1, append(X, [A], X1), append(Y, X, Y1), whl1(A1,B,X1,Y1,A2,B2,X2,Y2)
    let X = &generateVarFromCount(count, VarType::List);
    let Y1 = &generateVarFromCount(count, VarType::List);
    let B = &generateVarFromCount(count, VarType::Int);
    let A1 = &generateVarFromCount(count, VarType::Int);
    let Y = &generateVarFromCount(count, VarType::List);
    let new_8 = &generateVarFromCount(count, VarType::List);
    let X2 = &generateVarFromCount(count, VarType::List);
    let A = &generateVarFromCount(count, VarType::Int);
    let Y2 = &generateVarFromCount(count, VarType::List);
    let A2 = &generateVarFromCount(count, VarType::Int);
    let X1 = &generateVarFromCount(count, VarType::List);
    let B2 = &generateVarFromCount(count, VarType::Int);
    let cond1 = format!("(and <(eq {A} {new_0}) (eq {B} {new_1}) (eq {X} {new_2}) (eq {Y} {new_3}) (eq {A2} {new_4}) (eq {B2} {new_5}) (eq {X2} {new_6}) (eq {Y2} {new_7}) (eq (list {A} (emptyList)) {new_8}) (leq {A} (minus {B} 1)) (eq {A1} (add {A} 1))>)");
    let chc1 = format!(
        "(new {syntax} {cond1} <{} {} {}>)",
        appendDummy(new_2, new_8, X1),
        appendDummy(new_3, new_2, Y1),
        whl1Dummy(A1, new_1, X1, Y1, new_4, new_5, new_6, new_7)
    );
    let chc1AppId = eg.addExpr(&chc1);
    eg.shrink_slots(&eg.find_applied_id(&chc1AppId), &syntaxAppId.slots(), ());

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
    format!("(composeInit ifte {syntax} (true) <4 5 6 7>)")
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
    let X = &generateVarFromCount(count, VarType::List);
    let A = &generateVarFromCount(count, VarType::Int);
    let Y = &generateVarFromCount(count, VarType::List);
    let B = &generateVarFromCount(count, VarType::Int);
    let cond0 = format!(
        "(and <(eq {A} {new_4}) (eq {B} {new_5}) (eq {X} {new_6}) (eq {Y} {new_7}) (geq {A} {B})>)"
    );
    let chc0 = format!("(new {syntax} {cond0} <>)");
    let chc0AppId = eg.addExpr(&chc0);
    eg.shrink_slots(&eg.find_applied_id(&chc0AppId), &syntaxAppId.slots(), ());

    // ifte(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-1,    append(X, [A], X1), whl2(A,B,X1,Y,A2,B2,X2,Y2)
    let X = &generateVarFromCount(count, VarType::List);
    let B = &generateVarFromCount(count, VarType::Int);
    let Y = &generateVarFromCount(count, VarType::List);
    let new_8 = &generateVarFromCount(count, VarType::List);
    let X2 = &generateVarFromCount(count, VarType::List);
    let A = &generateVarFromCount(count, VarType::Int);
    let Y2 = &generateVarFromCount(count, VarType::List);
    let A2 = &generateVarFromCount(count, VarType::Int);
    let X1 = &generateVarFromCount(count, VarType::List);
    let B2 = &generateVarFromCount(count, VarType::Int);
    let cond1 = format!("(and <(eq {A} {new_0}) (eq {B} {new_1}) (eq {X} {new_2}) (eq {Y} {new_3}) (eq {A2} {new_4}) (eq {B2} {new_5}) (eq {X2} {new_6}) (eq {Y2} {new_7}) (eq (list {A} (emptyList)) {new_8}) (leq {A} (minus {B} 1))>)");
    let chc1 = format!(
        "(new {syntax} {cond1} <{} {}>)",
        appendDummy(new_2, new_8, X1),
        whl2Dummy(new_0, new_1, X1, new_3, new_4, new_5, new_6, new_7)
    );
    let chc1AppId = eg.addExpr(&chc1);
    eg.shrink_slots(&eg.find_applied_id(&chc1AppId), &syntaxAppId.slots(), ());

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
    format!("(composeInit whl2 {syntax} (true) <4 5 6 7>)")
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
    let X = &generateVarFromCount(count, VarType::List);
    let B = &generateVarFromCount(count, VarType::Int);
    let Y = &generateVarFromCount(count, VarType::List);
    let A = &generateVarFromCount(count, VarType::Int);
    let Y2 = &generateVarFromCount(count, VarType::List);
    let A2 = &generateVarFromCount(count, VarType::Int);
    let cond0 = format!("(and <(eq {A} {new_0}) (eq {B} {new_5}) (eq {X} {new_6}) (eq {Y} {new_3}) (eq {A2} {new_4}) (eq {Y2} {new_7}) (geq {A} (minus {B} 1)) (eq {A2} (add {A} 1))>)");
    let chc0 = format!(
        "(new {syntax} {cond0} <{}>)",
        appendDummy(new_3, new_6, new_7)
    );
    let chc0AppId = eg.addExpr(&chc0);
    eg.shrink_slots(&eg.find_applied_id(&chc0AppId), &syntaxAppId.slots(), ());

    // whl2(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-2,    A1 = A + 1,    append(X, [A1], X1),    append(Y, X, Y1),    whl2(A1,B,X1,Y1,A2,B2,X2,Y2)
    let X = &generateVarFromCount(count, VarType::List);
    let Y1 = &generateVarFromCount(count, VarType::List);
    let B = &generateVarFromCount(count, VarType::Int);
    let A1 = &generateVarFromCount(count, VarType::Int);
    let Y = &generateVarFromCount(count, VarType::List);
    let new_8 = &generateVarFromCount(count, VarType::List);
    let X2 = &generateVarFromCount(count, VarType::List);
    let A = &generateVarFromCount(count, VarType::Int);
    let Y2 = &generateVarFromCount(count, VarType::List);
    let A2 = &generateVarFromCount(count, VarType::Int);
    let X1 = &generateVarFromCount(count, VarType::List);
    let B2 = &generateVarFromCount(count, VarType::Int);
    let cond1 = format!("(and <(eq {A} {new_0}) (eq {B} {new_1}) (eq {X} {new_2}) (eq {Y} {new_3}) (eq {A2} {new_4}) (eq {B2} {new_5}) (eq {X2} {new_6}) (eq {Y2} {new_7}) (eq (list {A1} (emptyList)) {new_8}) (leq {A} (minus {B} 2)) (eq {A1} (add {A} 1))>)");
    let chc1 = format!(
        "(new {syntax} {cond1} <{} {} {}>)",
        appendDummy(new_2, new_8, X1),
        appendDummy(new_3, new_2, Y1),
        whl2Dummy(A1, new_1, X1, Y1, new_4, new_5, new_6, new_7)
    );
    let chc1AppId = eg.addExpr(&chc1);
    eg.shrink_slots(&eg.find_applied_id(&chc1AppId), &syntaxAppId.slots(), ());

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
    format!("(composeInit sum_list {syntax} (true) <1>)")
}

fn sum_listCHC(new_0: &str, new_1: &str, count: &mut u32, eg: &mut CHCEGraph) -> AppliedId {
    let syntax = format!("(pred <{new_0} {new_1}>)");

    let syntaxAppId = eg.addExpr(&syntax);
    // sum_list([], 0)
    let cond0 = format!("(and <(eq (emptyList) {new_0}) (eq 0 {new_1})>)");
    let chc0 = format!("(new {syntax} {cond0} <>)");
    let chc0AppId = eg.addExpr(&chc0);
    eg.shrink_slots(&eg.find_applied_id(&chc0AppId), &syntaxAppId.slots(), ());

    // sum_list([H|T], S) :- sum_list(T, S1), S = H + S1
    let S1 = &generateVarFromCount(count, VarType::Int);
    let T = &generateVarFromCount(count, VarType::List);
    let S = &generateVarFromCount(count, VarType::Int);
    let H = &generateVarFromCount(count, VarType::Int);
    let cond1 =
        format!("(and <(eq (list {H} {T}) {new_0}) (eq {S} {new_1}) (eq {S} (add {H} {S1}))>)");
    let chc1 = format!("(new {syntax} {cond1} <{}>)", sum_listDummy(T, S1));
    let chc1AppId = eg.addExpr(&chc1);
    eg.shrink_slots(&eg.find_applied_id(&chc1AppId), &syntaxAppId.slots(), ());

    let composeStr = format!("(compose <{chc0} {chc1}>)");
    let composeId = eg.addExpr(&composeStr);
    let dummyId = eg.addExpr(&sum_listDummy(new_0, new_1));
    eg.union(&composeId, &dummyId);
    composeId
}

fn incorrectDummy() -> String {
    let syntax = format!("(pred <>)");
    format!("(composeInit incorrect {syntax} (false) <>)")
}

fn incorrectCHC(count: &mut u32, eg: &mut CHCEGraph) -> AppliedId {
    let syntax = format!("(pred <>)");

    let syntaxAppId = eg.addExpr(&syntax);
    // incorrect :- N1 =\= N2, sum_list(X1, N1), sum_list(X2, N2), whl1(A,B,X,Y,A1,B1,X1,Y1), ifte(A, B,X,Y,A2,B2,X2,Y2)
    let X = &generateVarFromCount(count, VarType::List);
    let Y1 = &generateVarFromCount(count, VarType::List);
    let B1 = &generateVarFromCount(count, VarType::Int);
    let B = &generateVarFromCount(count, VarType::Int);
    let A1 = &generateVarFromCount(count, VarType::Int);
    let A2 = &generateVarFromCount(count, VarType::Int);
    let Y = &generateVarFromCount(count, VarType::List);
    let X2 = &generateVarFromCount(count, VarType::List);
    let A = &generateVarFromCount(count, VarType::Int);
    let Y2 = &generateVarFromCount(count, VarType::List);
    let N1 = &generateVarFromCount(count, VarType::Int);
    let N2 = &generateVarFromCount(count, VarType::Int);
    let X1 = &generateVarFromCount(count, VarType::List);
    let B2 = &generateVarFromCount(count, VarType::Int);
    let cond0 = format!("(and <(neq {N1} {N2})>)");
    let chc0 = format!(
        "(new {syntax} {cond0} <{} {} {} {}>)",
        sum_listDummy(X1, N1),
        sum_listDummy(X2, N2),
        whl1Dummy(A, B, X, Y, A1, B1, X1, Y1),
        ifteDummy(A, B, X, Y, A2, B2, X2, Y2)
    );
    let chc0AppId = eg.addExpr(&chc0);
    eg.shrink_slots(&eg.find_applied_id(&chc0AppId), &syntaxAppId.slots(), ());

    let composeStr = format!("(compose <{chc0}>)");
    let composeId = eg.addExpr(&composeStr);
    let dummyId = eg.addExpr(&incorrectDummy());
    eg.union(&composeId, &dummyId);
    composeId
}

fn buildCHC(mut eg: CHCEGraph, count: &mut u32) -> (AppliedId, CHCRunner) {
    let new_0 = &generateVarFromCount(count, VarType::List);
    let new_1 = &generateVarFromCount(count, VarType::List);
    let new_2 = &generateVarFromCount(count, VarType::List);
    let appendDummyId = eg.addExpr(&appendDummy(new_0, new_1, new_2));
    let appendId = appendCHC(new_0, new_1, new_2, count, &mut eg);
    eg.union(&appendId, &appendDummyId);

    let new_0 = &generateVarFromCount(count, VarType::Int);
    let new_1 = &generateVarFromCount(count, VarType::Int);
    let new_2 = &generateVarFromCount(count, VarType::List);
    let new_3 = &generateVarFromCount(count, VarType::List);
    let new_4 = &generateVarFromCount(count, VarType::Int);
    let new_5 = &generateVarFromCount(count, VarType::Int);
    let new_6 = &generateVarFromCount(count, VarType::List);
    let new_7 = &generateVarFromCount(count, VarType::List);
    let whl1DummyId = eg.addExpr(&whl1Dummy(
        new_0, new_1, new_2, new_3, new_4, new_5, new_6, new_7,
    ));
    let whl1Id = whl1CHC(
        new_0, new_1, new_2, new_3, new_4, new_5, new_6, new_7, count, &mut eg,
    );
    eg.union(&whl1Id, &whl1DummyId);

    let new_0 = &generateVarFromCount(count, VarType::Int);
    let new_1 = &generateVarFromCount(count, VarType::Int);
    let new_2 = &generateVarFromCount(count, VarType::List);
    let new_3 = &generateVarFromCount(count, VarType::List);
    let new_4 = &generateVarFromCount(count, VarType::Int);
    let new_5 = &generateVarFromCount(count, VarType::Int);
    let new_6 = &generateVarFromCount(count, VarType::List);
    let new_7 = &generateVarFromCount(count, VarType::List);
    let ifteDummyId = eg.addExpr(&ifteDummy(
        new_0, new_1, new_2, new_3, new_4, new_5, new_6, new_7,
    ));
    let ifteId = ifteCHC(
        new_0, new_1, new_2, new_3, new_4, new_5, new_6, new_7, count, &mut eg,
    );
    eg.union(&ifteId, &ifteDummyId);

    let new_0 = &generateVarFromCount(count, VarType::Int);
    let new_1 = &generateVarFromCount(count, VarType::Int);
    let new_2 = &generateVarFromCount(count, VarType::List);
    let new_3 = &generateVarFromCount(count, VarType::List);
    let new_4 = &generateVarFromCount(count, VarType::Int);
    let new_5 = &generateVarFromCount(count, VarType::Int);
    let new_6 = &generateVarFromCount(count, VarType::List);
    let new_7 = &generateVarFromCount(count, VarType::List);
    let whl2DummyId = eg.addExpr(&whl2Dummy(
        new_0, new_1, new_2, new_3, new_4, new_5, new_6, new_7,
    ));
    let whl2Id = whl2CHC(
        new_0, new_1, new_2, new_3, new_4, new_5, new_6, new_7, count, &mut eg,
    );
    eg.union(&whl2Id, &whl2DummyId);

    let new_0 = &generateVarFromCount(count, VarType::List);
    let new_1 = &generateVarFromCount(count, VarType::Int);
    let sum_listDummyId = eg.addExpr(&sum_listDummy(new_0, new_1));
    let sum_listId = sum_listCHC(new_0, new_1, count, &mut eg);
    eg.union(&sum_listId, &sum_listDummyId);

    let incorrectDummyId = eg.addExpr(&incorrectDummy());
    let incorrectId = incorrectCHC(count, &mut eg);
    eg.union(&incorrectId, &incorrectDummyId);

    dumpCHCEGraph(&eg);

    let mut runner: CHCRunner = Runner::default()
        .with_egraph(eg)
        .with_iter_limit(ITER_LIMIT)
        .with_time_limit(Duration::from_secs(TIME_LIMIT_SECS));
    let (report, t): (Report, _) = time(|| {
        runner.run(&mut getAllRewrites(
            RewriteList::default(),
            DO_CONST_REWRITE,
            DO_FOLDING,
        ))
    });

    println!("use time {t:?}");
    println!("report {report:?}");

    println!("egraph after run");
    dumpCHCEGraph(&runner.egraph);
    runner.egraph.check();
    (incorrectId, runner)
}

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
