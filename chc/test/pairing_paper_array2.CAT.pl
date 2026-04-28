:- pred ff1.
:- pred constr(bool).
:- pred new1(int,int,int,int,int,int,int,int).
:- pred new11(int).
:- pred new2(int,int,int,int,int).
:- pred new3(int,int,int,int,int).
:- pred new4(int).
:- pred new7(int).
:- pred new9(int,int,int,int,int).

:- mode constr(in).
:- mode new1(out,out,in,in,out,out,out,out).
:- mode new11(out).
:- mode new2(out,in,in,out,out).
:- mode new3(out,in,in,out,out).
:- mode new4(out).
:- mode new7(in).
:- mode new9(out,in,in,out,out).

new9(A,B,C,D,C) :- (B>=C-1&D=B+1), new11(A).
new9(A,B,C,D,E) :- (B=<C-2&F=B+1), new9(A,F,C,D,E), new11(G), new7(F).
new7(A).
new7(A) :- new7(A).
new11(A) :- new4(A).
new11(A) :- new11(A).
new4(0).
new4(A) :- (A=B+C), new4(C).
new3(A,B,C,B,C) :- (B>=C), new4(A).
new3(A,B,C,D,E) :- (B=<C-1&F=B+1), new3(A,F,C,D,E), new11(G), new7(B).
new2(A,B,C,B,C) :- (B>=C), new4(A).
new2(A,B,C,D,E) :- (B=<C-1), new9(A,B,C,D,E), new7(B).
new1(A,B,C,D,E,F,G,H) :- new2(B,C,D,G,H), new3(A,C,D,E,F).
ff1 :- (~ (A=B)), new1(A,B,C,D,E,F,G,H).
