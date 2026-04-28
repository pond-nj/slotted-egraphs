:- pred ff1.
:- pred constr(bool).
:- pred new1(int,int,int,int).
:- pred new4(int,int,int,int).
:- pred new6(int).

:- mode constr(in).
:- mode new1(out,out,out,out).
:- mode new4(out,out,out,out).
:- mode new6(out).

new6(A) :- A=0.
new6(A) :- A=B+1, new6(B).
new4(A,A,B,C) :- B=0, C=0, new6(A).
new4(A,B,C,D) :- B=E+1, F=0, G=C-1, H=D-1, C>=0+1, D>=0+1, new4(A,E,G,H).
new1(A,B,C,D) :- A=0, B=0, C=0.
new1(A,B,C,D) :- E=C-1, C>=0+1, ((F<G&D>0)=> ~ (E=D)), new4(G,B,H,C), 
          new4(F,A,D,I), new1(F,G,E,D).
ff1 :- ((A<B&C>0)&D=C), new1(A,B,D,C).