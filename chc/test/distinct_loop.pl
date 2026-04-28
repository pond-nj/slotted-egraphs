:- pred loop(list(int),int).
:- mode loop(in, out).
:- cata loop/2-1.

:- pred constr(bool).
:- mode constr(in).
:- ignore constr/1.

:- pred ff1.
:- pred start(int).
:- mode start(in).

:- spec start(X) ==>
       loop(A1, N), loop(A2, M) =>
       constr(((N = 2) & (M = 100)) => (A1 = A2)).

start(X).
loop([], X) :- constr(X = 0).
loop([Z|A0], J) :- constr(((J > 0) & (J0 = J - 1)) & (Z = 0)), loop(A0, J0).
ff1 :- start(X), loop(A1, N), loop(A2, M), constr(((N = 2) & (M = 100)) & (A1 = A2)).