whl1ifte(A_1, B_1, X_1, Y_1, A_1, B_1, X_1, Y_1, A_2, B_2, X_2, Y_2, A_2, B_2, X_2, Y_2) :-
    A_1 >= B_1,
    A_2 >= B_2.

whl1ifte(A_1, B_1, X_1, Y_1, A_1, B_1, X_1, Y_1, A_2, B_2, X_2, Y_2, A2_2, B2_2, X2_2, Y2_2) :-
    A_1 >= B_1,
    A_2 =< B_2-1,
    append(X_2, [A_2], X1_2),
    whl2(A_2,B_2,X1_2,Y_2,A2_2,B2_2,X2_2,Y2_2).

whl1ifte(A_1, B_1, X_1, Y_1, A2_1, B2_1, X2_1, Y2_1, A_2, B_2, X_2, Y_2, A_2, B_2, X_2, Y_2) :-
    whl1ifte(A1_1, B_1, X1_1, Y1_1, A2_1, B2_1, X2_1, Y2_1, A_2, B_2, X_2, Y_2, A_2, B_2, X_2, Y_2),
    A_1 =< B_1-1,
    A1_1=A_1+1,
    append(X_1, [A_1], X1_1),
    append(Y_1, X_1, Y1_1),
    A_2 >= B_2.

whl1ifte(A_1, B_1, X_1, Y_1, A2_1, B2_1, X2_1, Y2_1, A_2, B_2, X_2, Y_2, A2_2, B2_2, X2_2, Y2_2) :-
    whl1ifte(A1_1, B_1, X1_1, Y1_1, A2_1, B2_1, X2_1, Y2_1, A_2, B_2, X_2, Y_2, A2_2, B2_2, X2_2, Y2_2),
    A_1 =< B_1-1,
    A1_1=A_1+1,
    append(X_1, [A_1], X1_1),
    append(Y_1, X_1, Y1_1),
    A_2 =< B_2-1,
    append(X_2, [A_2], X1_2),
    whl2(A_2,B_2,X1_2,Y_2,A2_2,B2_2,X2_2,Y2_2).

append([], X, X).
append([T|X], Y, [T|Z]) :- append(X, Y, Z).

whl2(A,B,X,Y,A2,B,X,Y2) :- A >= B-1, A2=A+1, 
    append(Y, X, Y2).
whl2(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-2, A1 = A + 1,
    append(X, [A1], X1), 
    append(Y, X, Y1),
    whl2(A1,B,X1,Y1,A2,B2,X2,Y2).

sum_list([], 0).
sum_list([H|T], S) :- sum_list(T, S1), S = H + S1.

ff1 :- ~(N1 = N2), sum_list(X1, N1), sum_list(X2, N2), whl1ifte(A,B,X,Y,A1,B1,X1,Y1, A, B,X,Y,A2,B2,X2,Y2).
