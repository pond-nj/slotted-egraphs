:- pred append(list(int), list(int), list(int)).
:- mode append(in, in, out).
append([], X, X).
append([T|X], Y, [T|Z]) :- append(X, Y, Z).

:- pred whl1(int, int, list(int), list(int), int, int, list(int), list(int)).
:- mode whl1(in, in, in, in, out, out, out, out).
whl1(A,B,X,Y,A,B,X,Y) :- constr(A >= B).
whl1(A,B,X,Y,A2,B2,X2,Y2) :- constr((A =< B-1) & (A1=A+1)), append(X, [A], X1), append(Y, X, Y1), whl1(A1,B,X1,Y1,A2,B2,X2,Y2). 

:- pred ifte(int, int, list(int), list(int), int, int, list(int), list(int)).
:- mode ifte(in, in, in, in, out, out, out, out).
ifte(A,B,X,Y,A,B,X,Y ) :- constr(A >= B).
ifte(A,B,X,Y,A2,B2,X2,Y2) :- constr(A =< B-1),
    append(X, [A], X1), whl2(A,B,X1,Y,A2,B2,X2,Y2).

:- pred whl2(int, int, list(int), list(int), int, int, list(int), list(int)).
:- mode whl2(in, in, in, in, out, out, out, out).
whl2(A,B,X,Y,A2,B,X,Y2) :- constr((A >= B-1) & (A2=A+1)), 
    append(Y, X, Y2).
whl2(A,B,X,Y,A2,B2,X2,Y2) :- constr((A =< B-2) & (A1 = A + 1)),
    append(X, [A1], X1), 
    append(Y, X, Y1),
    whl2(A1,B,X1,Y1,A2,B2,X2,Y2).

:- pred sum_list(list(int), int).
:- mode sum_list(in, out).
:- cata sum_list/2-1.
sum_list([], 0).
sum_list([H|T], S) :- sum_list(T, S1), constr(S = H + S1).

:- pred constr(bool).
:- mode constr(in).
:- ignore constr/1.

:- spec tmpPred(A,B,X,Y,A1,B1,X1,Y1, A2,B2,X2,Y2) ==>
       sum_list(X1, N1), sum_list(X2, N2) =>
       constr(N1 = N2).

:- pred tmpPred(int, int, list(int), list(int), int, int, list(int), list(int), int, int, list(int), list(int)).
:- mode tmpPred(in, in, in, in, out, out, out, out, out, out, out, out).
tmpPred(A,B,X,Y,A1,B1,X1,Y1, A2,B2,X2,Y2) :- whl1(A,B,X,Y,A1,B1,X1,Y1), ifte(A, B,X,Y,A2,B2,X2,Y2).

:- pred ff1.
ff1 :- constr(~(N1 = N2)), sum_list(X1, N1), sum_list(X2, N2), tmpPred(A,B,X,Y,A1,B1,X1,Y1, A2,B2,X2,Y2).
