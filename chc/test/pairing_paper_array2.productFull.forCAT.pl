:- pred all(list(int),int, list(int),int, int, int, list(int), list(int), int, int, list(int), list(int), int, int, list(int), list(int), int, int, list(int), list(int)).
:- mode all(in, out, in, out, in, in, in, in, out, out, out, out, in, in, in, in, out, out, out, out).
:- pred constr(bool).
:- mode constr(in).
:- ignore constr/1.

all([], 0, [], 0, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
    constr((A_3 >= B_3) & (A_4 >= B_4)).

all([], 0, [], 0, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
    constr((A_3 >= B_3) & (A_4 =< B_4-1)),
    append(X_4, [A_4], X1_4),
    whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).

all([], 0, [], 0, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
    all([], 0, [], 0, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4),
    constr(((A_3 =< B_3-1) & (A1_3=A_3+1)) & A_4 >= B_4)
    append(X_3, [A_3], X1_3),
    append(Y_3, X_3, Y1_3).

all([], 0, [], 0, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
    all([], 0, [], 0, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4),
    constr(((A_3 =< B_3-1) & (A1_3=A_3+1)) & A_4 =< B_4-1),
    append(X_3, [A_3], X1_3),
    append(Y_3, X_3, Y1_3),
    append(X_4, [A_4], X1_4),
    whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).

all([], 0, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
    sum_list(T1_2, S11_2),
    constr((S1_2 = H1_2 + S11_2) & (A_3 >= B_3) & (A_4 >= B_4)).

all([], 0, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
    sum_list(T1_2, S11_2),
    constr((S1_2 = H1_2 + S11_2) & (A_3 >= B_3) & (A_4 =< B_4-1)),
    append(X_4, [A_4], X1_4),
    whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).

all([], 0, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
    all([], 0, [H1_2|T1_2], S1_2, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4),
    sum_list(T1_2, S11_2),
    constr((S1_2 = H1_2 + S11_2) & (A_3 =< B_3-1) & (A1_3=A_3+1) & (A_4 >= B_4)),
    append(X_3, [A_3], X1_3),
    append(Y_3, X_3, Y1_3).

all([], 0, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
    all([], 0, [H1_2|T1_2], S1_2, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4),
    sum_list(T1_2, S11_2),
    constr((S1_2 = H1_2 + S11_2) & (A_3 =< B_3-1) & (A1_3=A_3+1) & (A_4 =< B_4-1)),
    append(X_3, [A_3], X1_3),
    append(Y_3, X_3, Y1_3),
    append(X_4, [A_4], X1_4),
    whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).

all([H_1|T_1], S_1, [], 0, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
    all(T_1, S1_1, [], 0, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4),
    constr((S_1 = H_1 + S1_1) & (A_3 >= B_3) & (A_4 >= B_4)).

all([H_1|T_1], S_1, [], 0, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
    all(T_1, S1_1, [], 0, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4),
    constr((S_1 = H_1 + S1_1) & (A_3 >= B_3) & (A_4 =< B_4-1)),
    append(X_4, [A_4], X1_4),
    whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).

all([H_1|T_1], S_1, [], 0, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
    all(T_1, S1_1, [], 0, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4),
    constr((S_1 = H_1 + S1_1) & (A_3 =< B_3-1) & (A1_3=A_3+1) & (A_4 >= B_4)),
    append(X_3, [A_3], X1_3),
    append(Y_3, X_3, Y1_3).

all([H_1|T_1], S_1, [], 0, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
    all(T_1, S1_1, [], 0, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4),
    constr((S_1 = H_1 + S1_1) & (A_3 =< B_3-1) & (A1_3=A_3+1) & (A_4 =< B_4-1)),
    append(X_3, [A_3], X1_3),
    append(Y_3, X_3, Y1_3),
    append(X_4, [A_4], X1_4),
    whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).

all([H_1|T_1], S_1, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
    all(T_1, S1_1, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4),
    constr((S_1 = H_1 + S1_1) & (S1_2 = H1_2 + S11_2) & (A_3 >= B_3) & (A_4 >= B_4)),
    sum_list(T1_2, S11_2).

all([H_1|T_1], S_1, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
    all(T_1, S1_1, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4),
    constr((S_1 = H_1 + S1_1) & (S1_2 = H1_2 + S11_2) & (A_3 >= B_3) & (A_4 =< B_4-1)),
    sum_list(T1_2, S11_2),
    append(X_4, [A_4], X1_4),
    whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).

all([H_1|T_1], S_1, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
    all(T_1, S1_1, [H1_2|T1_2], S1_2, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4),
    constr((S_1 = H_1 + S1_1) & (S1_2 = H1_2 + S11_2) & (A_3 =< B_3-1) & (A1_3=A_3+1) & (A_4 >= B_4)),
    sum_list(T1_2, S11_2),
    append(X_3, [A_3], X1_3),
    append(Y_3, X_3, Y1_3).

all([H_1|T_1], S_1, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
    all(T_1, S1_1, [H1_2|T1_2], S1_2, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4),
    constr((S_1 = H_1 + S1_1) & (S1_2 = H1_2 + S11_2) & (A_3 =< B_3-1) & (A1_3=A_3+1) & (A_4 =< B_4-1)),
    sum_list(T1_2, S11_2),
    append(X_3, [A_3], X1_3),
    append(Y_3, X_3, Y1_3),
    append(X_4, [A_4], X1_4),
    whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).


:- pred append(list(int), list(int), list(int)).
:- mode append(in, in, out).

append([], X, X).
append([T|X], Y, [T|Z]) :- append(X, Y, Z).

:- pred whl2(int, int, list(int), list(int), int, int, list(int), list(int)).
:- mode whl2(in, in, in, in, out, out, out, out).

whl2(A,B,X,Y,A2,B,X,Y2) :- 
    constr((A >= B-1) & (A2=A+1)), 
    append(Y, X, Y2).
whl2(A,B,X,Y,A2,B2,X2,Y2) :- 
    constr((A =< B-2) & (A1 = A + 1)),
    append(X, [A1], X1), 
    append(Y, X, Y1),
    whl2(A1,B,X1,Y1,A2,B2,X2,Y2).

:- pred sum_list(list(int), int).
:- mode sum_list(in, out).
:- cata sum_list/2-1.


sum_list([], 0).
sum_list([H|T], S) :- sum_list(T, S1), constr(S = H + S1).

:- pred sum_list1(list(int), int).
:- mode sum_list1(in, out).
:- cata sum_list1/2-1.

sum_list1([], 0).
sum_list1([H1|T1], S1) :- sum_list(T1, S11), constr(S1 = H1 + S11).

:- pred tmp(list(int), int).
:- mode tmp(in, out).
:- cata tmp/2-1.
tmp([], 0).

:- pred ff1.

:- spec all(X1, N1, X2, N2, A,B,X,Y,A1,B1,X1,Y1, A, B,X,Y,A2,B2,X2,Y2) ==>
       tmp(Z, W) =>
       constr(N1 = N2).

ff1 :- constr(~(N1 = N2)), tmp(Z, W), all(X1, N1, X2, N2, A,B,X,Y,A1,B1,X1,Y1, A, B,X,Y,A2,B2,X2,Y2).
