new1(A) :- (A=0).
new1(A) :- ((A>0&B=A-1)&C=0).
new12(A1) :- (A1=0).
new12(A1) :- ((A1>0&B1=A1-1)&C1=0).
ff1 :- ((A=2&B=100)&C=D), new1(B), new1(A).