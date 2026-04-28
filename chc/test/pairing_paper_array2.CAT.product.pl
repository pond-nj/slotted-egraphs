new23(A_1, B_1, C_1, B_1, C_1, A_2, B_2, C_2, B_2, C_2) :-
    (B_1>=C_1),
    new4(A_1),
    (B_2>=C_2),
    new4(A_2).

new23(A_1, B_1, C_1, B_1, C_1, A_2, B_2, C_2, D_2, E_2) :-
    new23(A_1, B_1, C_1, B_1, C_1, A_2, F_2, C_2, D_2, E_2),
    (B_1>=C_1),
    new4(A_1),
    (B_2=<C_2-1&F_2=B_2+1),
    new11(G_2),
    new7(B_2).

new23(A_1, B_1, C_1, D_1, E_1, A_2, B_2, C_2, B_2, C_2) :-
    (B_1=<C_1-1),
    new9(A_1,B_1,C_1,D_1,E_1),
    new7(B_1),
    (B_2>=C_2),
    new4(A_2).

new23(A_1, B_1, C_1, D_1, E_1, A_2, B_2, C_2, D_2, E_2) :-
    new23(A_1, B_1, C_1, D_1, E_1, A_2, F_2, C_2, D_2, E_2),
    (B_1=<C_1-1),
    new9(A_1,B_1,C_1,D_1,E_1),
    new7(B_1),
    (B_2=<C_2-1&F_2=B_2+1),
    new11(G_2),
    new7(B_2).

new9(A,B,C,D,C) :- (B>=C-1&D=B+1), new11(A).
new9(A,B,C,D,E) :- (B=<C-2&F=B+1), new9(A,F,C,D,E), new11(G), new7(F).
new7(A).
new7(A) :- new7(A).
new11(A) :- new4(A).
new11(A) :- new11(A).
new4(0).
new4(A) :- (A=B+C), new4(C).
new1(A,B,C,D,E,F,G,H) :- new23(B,C,D,G,H, A,C,D,E,F).
ff1 :- (~ (A=B)), new1(A,B,C,D,E,F,G,H).
