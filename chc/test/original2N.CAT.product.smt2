(set-logic HORN)
(declare-datatypes () ((List (mk-nil) (mk-cons (head Int) (tail List)))))
(declare-fun new1 (Int Int Int Int) Bool)
(declare-fun new4 (Int Int Int Int) Bool)
(declare-fun new441 (Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun new5 (Int Int Int Int) Bool)
(declare-fun new6 (Int) Bool)
; new441(A_1, A_1, B_1, C_1, A1_2, A1_2, B1_2, C1_2, A_3, B_3, C_3, D_3) :-
;     B_1=0,
;     C_1=0,
;     new6(A_1),
;     B1_2=0,
;     C1_2=0,
;     new6(A1_2),
;     A_3=0,
;     B_3=0,
;     C_3=0.
(assert (forall ((A_1 Int) (B_1 Int) (C_1 Int) (A1_2 Int) (B1_2 Int) (C1_2 Int) (A_3 Int) (B_3 Int) (C_3 Int) (D_3 Int)) (=> (and (= B_1 0) (= C_1 0) (new6 A_1) (= B1_2 0) (= C1_2 0) (new6 A1_2) (= A_3 0) (= B_3 0) (= C_3 0)) (new441 A_1 A_1 B_1 C_1 A1_2 A1_2 B1_2 C1_2 A_3 B_3 C_3 D_3))))
; new441(A_1, A_1, B_1, C_1, A1_2, A1_2, B1_2, C1_2, A_3, B_3, C_3, D_3) :-
;     new441(A_1, A_1, B_1, C_1, A1_2, A1_2, B1_2, C1_2, F_3, G_3, E_3, D_3),
;     B_1=0,
;     C_1=0,
;     new6(A_1),
;     B1_2=0,
;     C1_2=0,
;     new6(A1_2),
;     E_3=C_3-1,
;     C_3>=0+1,
;     ((F_3<G_3&D_3>0)=> ~ (E_3=D_3)),
;     new4(G_3,B_3,H_3,C_3),
;     new5(F_3,A_3,D_3,I_3).
(assert (forall ((A_1 Int) (B_1 Int) (C_1 Int) (A1_2 Int) (B1_2 Int) (C1_2 Int) (A_3 Int) (B_3 Int) (C_3 Int) (D_3 Int) (F_3 Int) (G_3 Int) (E_3 Int) (H_3 Int) (I_3 Int)) (=> (and (new441 A_1 A_1 B_1 C_1 A1_2 A1_2 B1_2 C1_2 F_3 G_3 E_3 D_3) (= B_1 0) (= C_1 0) (new6 A_1) (= B1_2 0) (= C1_2 0) (new6 A1_2) (= E_3 (- C_3 1)) (>= C_3 (+ 0 1)) (=> (and (< F_3 G_3) (> D_3 0)) (not (= E_3 D_3))) (new4 G_3 B_3 H_3 C_3) (new5 F_3 A_3 D_3 I_3)) (new441 A_1 A_1 B_1 C_1 A1_2 A1_2 B1_2 C1_2 A_3 B_3 C_3 D_3))))
; new441(A_1, A_1, B_1, C_1, A1_2, B1_2, C1_2, D1_2, A_3, B_3, C_3, D_3) :-
;     B_1=0,
;     C_1=0,
;     new6(A_1),
;     B1_2=E1_2+1,
;     F1_2=0,
;     G1_2=C1_2-1,
;     H1_2=D1_2-1,
;     C1_2>=0+1,
;     D1_2>=0+1,
;     new4(A1_2,E1_2,G1_2,H1_2),
;     A_3=0,
;     B_3=0,
;     C_3=0.
(assert (forall ((A_1 Int) (B_1 Int) (C_1 Int) (A1_2 Int) (B1_2 Int) (C1_2 Int) (D1_2 Int) (A_3 Int) (B_3 Int) (C_3 Int) (D_3 Int) (E1_2 Int) (F1_2 Int) (G1_2 Int) (H1_2 Int)) (=> (and (= B_1 0) (= C_1 0) (new6 A_1) (= B1_2 (+ E1_2 1)) (= F1_2 0) (= G1_2 (- C1_2 1)) (= H1_2 (- D1_2 1)) (>= C1_2 (+ 0 1)) (>= D1_2 (+ 0 1)) (new4 A1_2 E1_2 G1_2 H1_2) (= A_3 0) (= B_3 0) (= C_3 0)) (new441 A_1 A_1 B_1 C_1 A1_2 B1_2 C1_2 D1_2 A_3 B_3 C_3 D_3))))
; new441(A_1, A_1, B_1, C_1, A1_2, B1_2, C1_2, D1_2, A_3, B_3, C_3, D_3) :-
;     new441(A_1, A_1, B_1, C_1, A1_2, B1_2, C1_2, D1_2, F_3, G_3, E_3, D_3),
;     B_1=0,
;     C_1=0,
;     new6(A_1),
;     B1_2=E1_2+1,
;     F1_2=0,
;     G1_2=C1_2-1,
;     H1_2=D1_2-1,
;     C1_2>=0+1,
;     D1_2>=0+1,
;     new4(A1_2,E1_2,G1_2,H1_2),
;     E_3=C_3-1,
;     C_3>=0+1,
;     ((F_3<G_3&D_3>0)=> ~ (E_3=D_3)),
;     new4(G_3,B_3,H_3,C_3),
;     new5(F_3,A_3,D_3,I_3).
(assert (forall ((A_1 Int) (B_1 Int) (C_1 Int) (A1_2 Int) (B1_2 Int) (C1_2 Int) (D1_2 Int) (A_3 Int) (B_3 Int) (C_3 Int) (D_3 Int) (F_3 Int) (G_3 Int) (E_3 Int) (E1_2 Int) (F1_2 Int) (G1_2 Int) (H1_2 Int) (H_3 Int) (I_3 Int)) (=> (and (new441 A_1 A_1 B_1 C_1 A1_2 B1_2 C1_2 D1_2 F_3 G_3 E_3 D_3) (= B_1 0) (= C_1 0) (new6 A_1) (= B1_2 (+ E1_2 1)) (= F1_2 0) (= G1_2 (- C1_2 1)) (= H1_2 (- D1_2 1)) (>= C1_2 (+ 0 1)) (>= D1_2 (+ 0 1)) (new4 A1_2 E1_2 G1_2 H1_2) (= E_3 (- C_3 1)) (>= C_3 (+ 0 1)) (=> (and (< F_3 G_3) (> D_3 0)) (not (= E_3 D_3))) (new4 G_3 B_3 H_3 C_3) (new5 F_3 A_3 D_3 I_3)) (new441 A_1 A_1 B_1 C_1 A1_2 B1_2 C1_2 D1_2 A_3 B_3 C_3 D_3))))
; new441(A_1, B_1, C_1, D_1, A1_2, A1_2, B1_2, C1_2, A_3, B_3, C_3, D_3) :-
;     new441(A_1, E_1, G_1, H_1, A1_2, A1_2, B1_2, C1_2, A_3, B_3, C_3, D_3),
;     B_1=E_1+1,
;     F_1=0,
;     G_1=C_1-1,
;     H_1=D_1-1,
;     C_1>=0+1,
;     D_1>=0+1,
;     B1_2=0,
;     C1_2=0,
;     new6(A1_2),
;     A_3=0,
;     B_3=0,
;     C_3=0.
(assert (forall ((A_1 Int) (B_1 Int) (C_1 Int) (D_1 Int) (A1_2 Int) (B1_2 Int) (C1_2 Int) (A_3 Int) (B_3 Int) (C_3 Int) (D_3 Int) (E_1 Int) (G_1 Int) (H_1 Int) (F_1 Int)) (=> (and (new441 A_1 E_1 G_1 H_1 A1_2 A1_2 B1_2 C1_2 A_3 B_3 C_3 D_3) (= B_1 (+ E_1 1)) (= F_1 0) (= G_1 (- C_1 1)) (= H_1 (- D_1 1)) (>= C_1 (+ 0 1)) (>= D_1 (+ 0 1)) (= B1_2 0) (= C1_2 0) (new6 A1_2) (= A_3 0) (= B_3 0) (= C_3 0)) (new441 A_1 B_1 C_1 D_1 A1_2 A1_2 B1_2 C1_2 A_3 B_3 C_3 D_3))))
; new441(A_1, B_1, C_1, D_1, A1_2, A1_2, B1_2, C1_2, A_3, B_3, C_3, D_3) :-
;     new441(A_1, E_1, G_1, H_1, A1_2, A1_2, B1_2, C1_2, F_3, G_3, E_3, D_3),
;     B_1=E_1+1,
;     F_1=0,
;     G_1=C_1-1,
;     H_1=D_1-1,
;     C_1>=0+1,
;     D_1>=0+1,
;     B1_2=0,
;     C1_2=0,
;     new6(A1_2),
;     E_3=C_3-1,
;     C_3>=0+1,
;     ((F_3<G_3&D_3>0)=> ~ (E_3=D_3)),
;     new4(G_3,B_3,H_3,C_3),
;     new5(F_3,A_3,D_3,I_3).
(assert (forall ((A_1 Int) (B_1 Int) (C_1 Int) (D_1 Int) (A1_2 Int) (B1_2 Int) (C1_2 Int) (A_3 Int) (B_3 Int) (C_3 Int) (D_3 Int) (E_1 Int) (G_1 Int) (H_1 Int) (F_3 Int) (G_3 Int) (E_3 Int) (F_1 Int) (H_3 Int) (I_3 Int)) (=> (and (new441 A_1 E_1 G_1 H_1 A1_2 A1_2 B1_2 C1_2 F_3 G_3 E_3 D_3) (= B_1 (+ E_1 1)) (= F_1 0) (= G_1 (- C_1 1)) (= H_1 (- D_1 1)) (>= C_1 (+ 0 1)) (>= D_1 (+ 0 1)) (= B1_2 0) (= C1_2 0) (new6 A1_2) (= E_3 (- C_3 1)) (>= C_3 (+ 0 1)) (=> (and (< F_3 G_3) (> D_3 0)) (not (= E_3 D_3))) (new4 G_3 B_3 H_3 C_3) (new5 F_3 A_3 D_3 I_3)) (new441 A_1 B_1 C_1 D_1 A1_2 A1_2 B1_2 C1_2 A_3 B_3 C_3 D_3))))
; new441(A_1, B_1, C_1, D_1, A1_2, B1_2, C1_2, D1_2, A_3, B_3, C_3, D_3) :-
;     new441(A_1, E_1, G_1, H_1, A1_2, B1_2, C1_2, D1_2, A_3, B_3, C_3, D_3),
;     B_1=E_1+1,
;     F_1=0,
;     G_1=C_1-1,
;     H_1=D_1-1,
;     C_1>=0+1,
;     D_1>=0+1,
;     B1_2=E1_2+1,
;     F1_2=0,
;     G1_2=C1_2-1,
;     H1_2=D1_2-1,
;     C1_2>=0+1,
;     D1_2>=0+1,
;     new4(A1_2,E1_2,G1_2,H1_2),
;     A_3=0,
;     B_3=0,
;     C_3=0.
(assert (forall ((A_1 Int) (B_1 Int) (C_1 Int) (D_1 Int) (A1_2 Int) (B1_2 Int) (C1_2 Int) (D1_2 Int) (A_3 Int) (B_3 Int) (C_3 Int) (D_3 Int) (E_1 Int) (G_1 Int) (H_1 Int) (F_1 Int) (E1_2 Int) (F1_2 Int) (G1_2 Int) (H1_2 Int)) (=> (and (new441 A_1 E_1 G_1 H_1 A1_2 B1_2 C1_2 D1_2 A_3 B_3 C_3 D_3) (= B_1 (+ E_1 1)) (= F_1 0) (= G_1 (- C_1 1)) (= H_1 (- D_1 1)) (>= C_1 (+ 0 1)) (>= D_1 (+ 0 1)) (= B1_2 (+ E1_2 1)) (= F1_2 0) (= G1_2 (- C1_2 1)) (= H1_2 (- D1_2 1)) (>= C1_2 (+ 0 1)) (>= D1_2 (+ 0 1)) (new4 A1_2 E1_2 G1_2 H1_2) (= A_3 0) (= B_3 0) (= C_3 0)) (new441 A_1 B_1 C_1 D_1 A1_2 B1_2 C1_2 D1_2 A_3 B_3 C_3 D_3))))
; new441(A_1, B_1, C_1, D_1, A1_2, B1_2, C1_2, D1_2, A_3, B_3, C_3, D_3) :-
;     new441(A_1, E_1, G_1, H_1, A1_2, B1_2, C1_2, D1_2, F_3, G_3, E_3, D_3),
;     B_1=E_1+1,
;     F_1=0,
;     G_1=C_1-1,
;     H_1=D_1-1,
;     C_1>=0+1,
;     D_1>=0+1,
;     B1_2=E1_2+1,
;     F1_2=0,
;     G1_2=C1_2-1,
;     H1_2=D1_2-1,
;     C1_2>=0+1,
;     D1_2>=0+1,
;     new4(A1_2,E1_2,G1_2,H1_2),
;     E_3=C_3-1,
;     C_3>=0+1,
;     ((F_3<G_3&D_3>0)=> ~ (E_3=D_3)),
;     new4(G_3,B_3,H_3,C_3),
;     new5(F_3,A_3,D_3,I_3).
(assert (forall ((A_1 Int) (B_1 Int) (C_1 Int) (D_1 Int) (A1_2 Int) (B1_2 Int) (C1_2 Int) (D1_2 Int) (A_3 Int) (B_3 Int) (C_3 Int) (D_3 Int) (E_1 Int) (G_1 Int) (H_1 Int) (F_3 Int) (G_3 Int) (E_3 Int) (F_1 Int) (E1_2 Int) (F1_2 Int) (G1_2 Int) (H1_2 Int) (H_3 Int) (I_3 Int)) (=> (and (new441 A_1 E_1 G_1 H_1 A1_2 B1_2 C1_2 D1_2 F_3 G_3 E_3 D_3) (= B_1 (+ E_1 1)) (= F_1 0) (= G_1 (- C_1 1)) (= H_1 (- D_1 1)) (>= C_1 (+ 0 1)) (>= D_1 (+ 0 1)) (= B1_2 (+ E1_2 1)) (= F1_2 0) (= G1_2 (- C1_2 1)) (= H1_2 (- D1_2 1)) (>= C1_2 (+ 0 1)) (>= D1_2 (+ 0 1)) (new4 A1_2 E1_2 G1_2 H1_2) (= E_3 (- C_3 1)) (>= C_3 (+ 0 1)) (=> (and (< F_3 G_3) (> D_3 0)) (not (= E_3 D_3))) (new4 G_3 B_3 H_3 C_3) (new5 F_3 A_3 D_3 I_3)) (new441 A_1 B_1 C_1 D_1 A1_2 B1_2 C1_2 D1_2 A_3 B_3 C_3 D_3))))
; new6(A) :- A=0.
(assert (forall ((A Int)) (=> (and (= A 0)) (new6 A))))
; new6(A) :- A=B+1, new6(B).
(assert (forall ((A Int) (B Int)) (=> (and (= A (+ B 1)) (new6 B)) (new6 A))))
; new4(A,A,B,C) :- B=0, C=0, new6(A).
(assert (forall ((A Int) (B Int) (C Int)) (=> (and (= B 0) (= C 0) (new6 A)) (new4 A A B C))))
; new4(A,B,C,D) :- B=E+1, F=0, G=C-1, H=D-1, C>=0+1, D>=0+1, new4(A,E,G,H).
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int)) (=> (and (= B (+ E 1)) (= F 0) (= G (- C 1)) (= H (- D 1)) (>= C (+ 0 1)) (>= D (+ 0 1)) (new4 A E G H)) (new4 A B C D))))
; new5(A1,A1,B1,C1) :- B1=0, C1=0, new6(A1).
(assert (forall ((A1 Int) (B1 Int) (C1 Int)) (=> (and (= B1 0) (= C1 0) (new6 A1)) (new5 A1 A1 B1 C1))))
; new5(A1,B1,C1,D1) :- B1=E1+1, F1=0, G1=C1-1, H1=D1-1, C1>=0+1, D1>=0+1, new4(A1,E1,G1,H1).
(assert (forall ((A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int)) (=> (and (= B1 (+ E1 1)) (= F1 0) (= G1 (- C1 1)) (= H1 (- D1 1)) (>= C1 (+ 0 1)) (>= D1 (+ 0 1)) (new4 A1 E1 G1 H1)) (new5 A1 B1 C1 D1))))
; new1(A,B,C,D) :- A=0, B=0, C=0.
(assert (forall ((A Int) (B Int) (C Int) (D Int)) (=> (and (= A 0) (= B 0) (= C 0)) (new1 A B C D))))
; new1(A,B,C,D) :- E=C-1, C>=0+1, ((F<G&D>0)=> ~ (E=D)), new441(G,B,H,C,F,A,D,I,F,G,E,D).
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int)) (=> (and (= E (- C 1)) (>= C (+ 0 1)) (=> (and (< F G) (> D 0)) (not (= E D))) (new441 G B H C F A D I F G E D)) (new1 A B C D))))
; ff1 :- ((A<B&C>0)&D=C), new1(A,B,D,C).
(assert (forall ((A Int) (B Int) (C Int) (D Int)) (not (and (and (and (< A B) (> C 0)) (= D C)) (new1 A B D C)))))
(check-sat)