(set-logic HORN)
(declare-datatypes () ((List (mk-nil) (mk-cons (head Int) (tail List)))))
(declare-fun append (List List List) Bool)
(declare-fun sum_list (List Int) Bool)
(declare-fun whl1ifte (Int Int List List Int Int List List Int Int List List Int Int List List) Bool)
(declare-fun whl2 (Int Int List List Int Int List List) Bool)
; whl1ifte(A_1, B_1, X_1, Y_1, A_1, B_1, X_1, Y_1, A_2, B_2, X_2, Y_2, A_2, B_2, X_2, Y_2) :-
;     A_1 >= B_1,
;     A_2 >= B_2.
(assert (forall ((A_1 Int) (B_1 Int) (X_1 List) (Y_1 List) (A_2 Int) (B_2 Int) (X_2 List) (Y_2 List)) (=> (and (>= A_1 B_1) (>= A_2 B_2)) (whl1ifte A_1 B_1 X_1 Y_1 A_1 B_1 X_1 Y_1 A_2 B_2 X_2 Y_2 A_2 B_2 X_2 Y_2))))
; whl1ifte(A_1, B_1, X_1, Y_1, A_1, B_1, X_1, Y_1, A_2, B_2, X_2, Y_2, A2_2, B2_2, X2_2, Y2_2) :-
;     A_1 >= B_1,
;     A_2 =< B_2-1,
;     append(X_2, [A_2], X1_2),
;     whl2(A_2,B_2,X1_2,Y_2,A2_2,B2_2,X2_2,Y2_2).
(assert (forall ((A_1 Int) (B_1 Int) (X_1 List) (Y_1 List) (A_2 Int) (B_2 Int) (X_2 List) (Y_2 List) (A2_2 Int) (B2_2 Int) (X2_2 List) (Y2_2 List) (X1_2 List)) (=> (and (>= A_1 B_1) (<= A_2 (- B_2 1)) (append X_2 (mk-cons A_2 mk-nil) X1_2) (whl2 A_2 B_2 X1_2 Y_2 A2_2 B2_2 X2_2 Y2_2)) (whl1ifte A_1 B_1 X_1 Y_1 A_1 B_1 X_1 Y_1 A_2 B_2 X_2 Y_2 A2_2 B2_2 X2_2 Y2_2))))
; whl1ifte(A_1, B_1, X_1, Y_1, A2_1, B2_1, X2_1, Y2_1, A_2, B_2, X_2, Y_2, A_2, B_2, X_2, Y_2) :-
;     whl1ifte(A1_1, B_1, X1_1, Y1_1, A2_1, B2_1, X2_1, Y2_1, A_2, B_2, X_2, Y_2, A_2, B_2, X_2, Y_2),
;     A_1 =< B_1-1,
;     A1_1=A_1+1,
;     append(X_1, [A_1], X1_1),
;     append(Y_1, X_1, Y1_1),
;     A_2 >= B_2.
(assert (forall ((A_1 Int) (B_1 Int) (X_1 List) (Y_1 List) (A2_1 Int) (B2_1 Int) (X2_1 List) (Y2_1 List) (A_2 Int) (B_2 Int) (X_2 List) (Y_2 List) (A1_1 Int) (X1_1 List) (Y1_1 List)) (=> (and (whl1ifte A1_1 B_1 X1_1 Y1_1 A2_1 B2_1 X2_1 Y2_1 A_2 B_2 X_2 Y_2 A_2 B_2 X_2 Y_2) (<= A_1 (- B_1 1)) (= A1_1 (+ A_1 1)) (append X_1 (mk-cons A_1 mk-nil) X1_1) (append Y_1 X_1 Y1_1) (>= A_2 B_2)) (whl1ifte A_1 B_1 X_1 Y_1 A2_1 B2_1 X2_1 Y2_1 A_2 B_2 X_2 Y_2 A_2 B_2 X_2 Y_2))))
; whl1ifte(A_1, B_1, X_1, Y_1, A2_1, B2_1, X2_1, Y2_1, A_2, B_2, X_2, Y_2, A2_2, B2_2, X2_2, Y2_2) :-
;     whl1ifte(A1_1, B_1, X1_1, Y1_1, A2_1, B2_1, X2_1, Y2_1, A_2, B_2, X_2, Y_2, A2_2, B2_2, X2_2, Y2_2),
;     A_1 =< B_1-1,
;     A1_1=A_1+1,
;     append(X_1, [A_1], X1_1),
;     append(Y_1, X_1, Y1_1),
;     A_2 =< B_2-1,
;     append(X_2, [A_2], X1_2),
;     whl2(A_2,B_2,X1_2,Y_2,A2_2,B2_2,X2_2,Y2_2).
(assert (forall ((A_1 Int) (B_1 Int) (X_1 List) (Y_1 List) (A2_1 Int) (B2_1 Int) (X2_1 List) (Y2_1 List) (A_2 Int) (B_2 Int) (X_2 List) (Y_2 List) (A2_2 Int) (B2_2 Int) (X2_2 List) (Y2_2 List) (A1_1 Int) (X1_1 List) (Y1_1 List) (X1_2 List)) (=> (and (whl1ifte A1_1 B_1 X1_1 Y1_1 A2_1 B2_1 X2_1 Y2_1 A_2 B_2 X_2 Y_2 A2_2 B2_2 X2_2 Y2_2) (<= A_1 (- B_1 1)) (= A1_1 (+ A_1 1)) (append X_1 (mk-cons A_1 mk-nil) X1_1) (append Y_1 X_1 Y1_1) (<= A_2 (- B_2 1)) (append X_2 (mk-cons A_2 mk-nil) X1_2) (whl2 A_2 B_2 X1_2 Y_2 A2_2 B2_2 X2_2 Y2_2)) (whl1ifte A_1 B_1 X_1 Y_1 A2_1 B2_1 X2_1 Y2_1 A_2 B_2 X_2 Y_2 A2_2 B2_2 X2_2 Y2_2))))
; append([], X, X).
(assert (forall ((X List)) (=> true (append mk-nil X X))))
; append([T|X], Y, [T|Z]) :- append(X, Y, Z).
(assert (forall ((T Int) (X List) (Y List) (Z List)) (=> (and (append X Y Z)) (append (mk-cons T X) Y (mk-cons T Z)))))
; whl2(A,B,X,Y,A2,B,X,Y2) :- A >= B-1, A2=A+1,
;     append(Y, X, Y2).
(assert (forall ((A Int) (B Int) (X List) (Y List) (A2 Int) (Y2 List)) (=> (and (>= A (- B 1)) (= A2 (+ A 1)) (append Y X Y2)) (whl2 A B X Y A2 B X Y2))))
; whl2(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-2, A1 = A + 1,
;     append(X, [A1], X1),
;     append(Y, X, Y1),
;     whl2(A1,B,X1,Y1,A2,B2,X2,Y2).
(assert (forall ((A Int) (B Int) (X List) (Y List) (A2 Int) (B2 Int) (X2 List) (Y2 List) (A1 Int) (X1 List) (Y1 List)) (=> (and (<= A (- B 2)) (= A1 (+ A 1)) (append X (mk-cons A1 mk-nil) X1) (append Y X Y1) (whl2 A1 B X1 Y1 A2 B2 X2 Y2)) (whl2 A B X Y A2 B2 X2 Y2))))
; sum_list([], 0).
(assert (=> true (sum_list mk-nil 0)))
; sum_list([H|T], S) :- sum_list(T, S1), S = H + S1.
(assert (forall ((H Int) (T List) (S Int) (S1 Int)) (=> (and (sum_list T S1) (= S (+ H S1))) (sum_list (mk-cons H T) S))))
; ff1 :- ~(N1 = N2), sum_list(X1, N1), sum_list(X2, N2), whl1ifte(A,B,X,Y,A1,B1,X1,Y1, A, B,X,Y,A2,B2,X2,Y2).
(assert (forall ((N1 Int) (N2 Int) (X1 List) (X2 List) (A Int) (B Int) (X List) (Y List) (A1 Int) (B1 Int) (Y1 List) (A2 Int) (B2 Int) (Y2 List)) (not (and (not (= N1 N2)) (sum_list X1 N1) (sum_list X2 N2) (whl1ifte A B X Y A1 B1 X1 Y1 A B X Y A2 B2 X2 Y2)))))
(check-sat)