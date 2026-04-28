new([], Res_1, [], Res_2, [], []) :-
    constr(Res_1),
    constr(Res_2).

new([], Res_1, [], Res_2, [H_3|T_3], R_3) :-
    new([], Res_1, [], Res_2, T_3, S_3),
    constr(Res_1),
    constr(Res_2),
    snoc(S_3, H_3, R_3).

new([], Res_1, [H_2|T_2], Res_2, [], []) :-
    new([], Res_1, T_2, ResT_2, [], []),
    constr(Res_1),
    hd(T_2, IsDefT_2, HdT_2),
    constr(Res_2 = (IsDefT_2 => ((H_2 >= HdT_2) & ResT_2))).

new([], Res_1, [H_2|T_2], Res_2, [H_3|T_3], R_3) :-
    new([], Res_1, T_2, ResT_2, T_3, S_3),
    constr(Res_1),
    hd(T_2, IsDefT_2, HdT_2),
    constr(Res_2 = (IsDefT_2 => ((H_2 >= HdT_2) & ResT_2))),
    snoc(S_3, H_3, R_3).

new([H_1|T_1], Res_1, [], Res_2, [], []) :-
    new(T_1, ResT_1, [], Res_2, [], []),
    hd(T_1, IsDefT_1, HdT_1),
    constr(Res_1 = (IsDefT_1 => ((H_1 =< HdT_1) & ResT_1))),
    constr(Res_2).

new([H_1|T_1], Res_1, [], Res_2, [H_3|T_3], R_3) :-
    new(T_1, ResT_1, [], Res_2, T_3, S_3),
    hd(T_1, IsDefT_1, HdT_1),
    constr(Res_1 = (IsDefT_1 => ((H_1 =< HdT_1) & ResT_1))),
    constr(Res_2),
    snoc(S_3, H_3, R_3).

new([H_1|T_1], Res_1, [H_2|T_2], Res_2, [], []) :-
    new(T_1, ResT_1, T_2, ResT_2, [], []),
    hd(T_1, IsDefT_1, HdT_1),
    constr(Res_1 = (IsDefT_1 => ((H_1 =< HdT_1) & ResT_1))),
    hd(T_2, IsDefT_2, HdT_2),
    constr(Res_2 = (IsDefT_2 => ((H_2 >= HdT_2) & ResT_2))).

new([H_1|T_1], Res_1, [H_2|T_2], Res_2, [H_3|T_3], R_3) :-
    new(T_1, ResT_1, T_2, ResT_2, T_3, S_3),
    hd(T_1, IsDefT_1, HdT_1),
    constr(Res_1 = (IsDefT_1 => ((H_1 =< HdT_1) & ResT_1))),
    hd(T_2, IsDefT_2, HdT_2),
    constr(Res_2 = (IsDefT_2 => ((H_2 >= HdT_2) & ResT_2))),
    snoc(S_3, H_3, R_3).

snoc([], X, [X]).
snoc([X|Xs], Y, [X|Zs]) :- snoc(Xs, Y, Zs).
hd([], IsDef, Hd)    :- constr((~IsDef) & (Hd = 0)).
hd([H|T], IsDef, Hd) :- constr(IsDef & (Hd = H)).
ff1 :-
    constr(BL & (~BR)),
    new(L, BL, R, BR, L, R).