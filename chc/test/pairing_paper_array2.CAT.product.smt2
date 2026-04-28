(set-logic HORN)
(declare-datatypes () ((List (mk-nil) (mk-cons (head Int) (tail List)))))
(declare-fun new1 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun new11 (Int) Bool)
(declare-fun new23 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun new4 (Int) Bool)
(declare-fun new7 (Int) Bool)
(declare-fun new9 (Int Int Int Int Int) Bool)
; new23(A_1, B_1, C_1, B_1, C_1, A_2, B_2, C_2, B_2, C_2) :-
;     (B_1>=C_1),
;     new4(A_1),
;     (B_2>=C_2),
;     new4(A_2).
(assert (forall ((A_1 Int) (B_1 Int) (C_1 Int) (A_2 Int) (B_2 Int) (C_2 Int)) (=> (and (>= B_1 C_1) (new4 A_1) (>= B_2 C_2) (new4 A_2)) (new23 A_1 B_1 C_1 B_1 C_1 A_2 B_2 C_2 B_2 C_2))))
; new23(A_1, B_1, C_1, B_1, C_1, A_2, B_2, C_2, D_2, E_2) :-
;     new23(A_1, B_1, C_1, B_1, C_1, A_2, F_2, C_2, D_2, E_2),
;     (B_1>=C_1),
;     new4(A_1),
;     (B_2=<C_2-1&F_2=B_2+1),
;     new11(G_2),
;     new7(B_2).
(assert (forall ((A_1 Int) (B_1 Int) (C_1 Int) (A_2 Int) (B_2 Int) (C_2 Int) (D_2 Int) (E_2 Int) (F_2 Int) (G_2 Int)) (=> (and (new23 A_1 B_1 C_1 B_1 C_1 A_2 F_2 C_2 D_2 E_2) (>= B_1 C_1) (new4 A_1) (and (<= B_2 (- C_2 1)) (= F_2 (+ B_2 1))) (new11 G_2) (new7 B_2)) (new23 A_1 B_1 C_1 B_1 C_1 A_2 B_2 C_2 D_2 E_2))))
; new23(A_1, B_1, C_1, D_1, E_1, A_2, B_2, C_2, B_2, C_2) :-
;     (B_1=<C_1-1),
;     new9(A_1,B_1,C_1,D_1,E_1),
;     new7(B_1),
;     (B_2>=C_2),
;     new4(A_2).
(assert (forall ((A_1 Int) (B_1 Int) (C_1 Int) (D_1 Int) (E_1 Int) (A_2 Int) (B_2 Int) (C_2 Int)) (=> (and (<= B_1 (- C_1 1)) (new9 A_1 B_1 C_1 D_1 E_1) (new7 B_1) (>= B_2 C_2) (new4 A_2)) (new23 A_1 B_1 C_1 D_1 E_1 A_2 B_2 C_2 B_2 C_2))))
; new23(A_1, B_1, C_1, D_1, E_1, A_2, B_2, C_2, D_2, E_2) :-
;     new23(A_1, B_1, C_1, D_1, E_1, A_2, F_2, C_2, D_2, E_2),
;     (B_1=<C_1-1),
;     new9(A_1,B_1,C_1,D_1,E_1),
;     new7(B_1),
;     (B_2=<C_2-1&F_2=B_2+1),
;     new11(G_2),
;     new7(B_2).
(assert (forall ((A_1 Int) (B_1 Int) (C_1 Int) (D_1 Int) (E_1 Int) (A_2 Int) (B_2 Int) (C_2 Int) (D_2 Int) (E_2 Int) (F_2 Int) (G_2 Int)) (=> (and (new23 A_1 B_1 C_1 D_1 E_1 A_2 F_2 C_2 D_2 E_2) (<= B_1 (- C_1 1)) (new9 A_1 B_1 C_1 D_1 E_1) (new7 B_1) (and (<= B_2 (- C_2 1)) (= F_2 (+ B_2 1))) (new11 G_2) (new7 B_2)) (new23 A_1 B_1 C_1 D_1 E_1 A_2 B_2 C_2 D_2 E_2))))
; new9(A,B,C,D,C) :- (B>=C-1&D=B+1), new11(A).
(assert (forall ((A Int) (B Int) (C Int) (D Int)) (=> (and (and (>= B (- C 1)) (= D (+ B 1))) (new11 A)) (new9 A B C D C))))
; new9(A,B,C,D,E) :- (B=<C-2&F=B+1), new9(A,F,C,D,E), new11(G), new7(F).
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int)) (=> (and (and (<= B (- C 2)) (= F (+ B 1))) (new9 A F C D E) (new11 G) (new7 F)) (new9 A B C D E))))
; new7(A).
(assert (forall ((A Int)) (=> true (new7 A))))
; new7(A) :- new7(A).
(assert (forall ((A Int)) (=> (and (new7 A)) (new7 A))))
; new11(A) :- new4(A).
(assert (forall ((A Int)) (=> (and (new4 A)) (new11 A))))
; new11(A) :- new11(A).
(assert (forall ((A Int)) (=> (and (new11 A)) (new11 A))))
; new4(0).
(assert (=> true (new4 0)))
; new4(A) :- (A=B+C), new4(C).
(assert (forall ((A Int) (B Int) (C Int)) (=> (and (= A (+ B C)) (new4 C)) (new4 A))))
; new1(A,B,C,D,E,F,G,H) :- new23(B,C,D,G,H, A,C,D,E,F).
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int)) (=> (and (new23 B C D G H A C D E F)) (new1 A B C D E F G H))))
; ff1 :- (~ (A=B)), new1(A,B,C,D,E,F,G,H).
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int)) (not (and (not (= A B)) (new1 A B C D E F G H)))))
(check-sat)