rev([], []).
rev([H|T], R) :- rev(T, S), snoc(S, H, R).
snoc([], X, [X]).
snoc([X|Xs], Y, [X|Zs]) :- snoc(Xs, Y, Zs).
hd([], IsDef, Hd)    :- constr((~IsDef) & (Hd = 0)).
hd([H|T], IsDef, Hd) :- constr(IsDef & (Hd = H)).
is_asorted([], Res)    :- constr(Res).
is_asorted([H|T], Res) :-
    hd(T, IsDefT, HdT),
    is_asorted(T, ResT),
    constr(Res = (IsDefT => ((H =< HdT) & ResT))).
is_dsorted([], Res)    :- constr(Res).
is_dsorted([H|T], Res) :-
    hd(T, IsDefT, HdT),
    is_dsorted(T, ResT),
    constr(Res = (IsDefT => ((H >= HdT) & ResT))).
leq_all(N,[],B) :-
  constr( B ).
leq_all(N,[X|Xs],B) :-
  constr( B = (N=<X & B1) ),
  leq_all(N,Xs,B1).
ff1 :-
    constr(BL & (~BR)),
    is_asorted(L, BL),
    is_dsorted(R, BR),
    rev(L, R).
