new7(A,B,C,D,E,F,G,H,D,I,J) :- (A&B=D), (C=(K=>(D>=L&M))), (E), (~F&G=0), (H), 
          (J=(I=<D&N)), (M), (~K&L=0), (N).
new7(A,B,C,D,E,F,G,H,D,I,J) :- (A&B=K), (C=(L=>(K>=M&N))), (E=(D=<K&O)), 
          (F&G=K), (H=(P=>(K>=Q&R))), (J=(I=<K&S)), (O=>R=N), 
          new7(L,M,N,D,O,P,Q,R,D,I,S).
new3(A,B,C,D,E,F) :- (A), (C), (~D&E=0), (F).
new3(A,B,C,D,E,F) :- (D&E=G), (F=(H=>(G=<I&J))), (J=K), (L=>K=A), 
          new7(M,N,A,G,L,O,P,K,G,B,C), new3(K,G,L,H,I,J).
ff1 :- (A& ~B), new3(B,C,D,E,F,A).
