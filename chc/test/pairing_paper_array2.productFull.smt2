(set-logic HORN)
(declare-datatypes () ((List (mk-nil) (mk-cons (head Int) (tail List)))))
(declare-fun all (List Int List Int Int Int List List Int Int List List Int Int List List Int Int List List) Bool)
(declare-fun append (List List List) Bool)
(declare-fun ifte (Int Int List List Int Int List List) Bool)
(declare-fun sum_list (List Int) Bool)
(declare-fun sum_list1 (List Int) Bool)
(declare-fun whl1 (Int Int List List Int Int List List) Bool)
(declare-fun whl2 (Int Int List List Int Int List List) Bool)
; all([], 0, [], 0, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
;     A_3 >= B_3,
;     A_4 >= B_4.
(assert (forall ((A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List)) (=> (and (>= A_3 B_3) (>= A_4 B_4)) (all mk-nil 0 mk-nil 0 A_3 B_3 X_3 Y_3 A_3 B_3 X_3 Y_3 A_4 B_4 X_4 Y_4 A_4 B_4 X_4 Y_4))))
; all([], 0, [], 0, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
;     A_3 >= B_3,
;     A_4 =< B_4-1,
;     append(X_4, [A_4], X1_4),
;     whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).
(assert (forall ((A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List) (A2_4 Int) (B2_4 Int) (X2_4 List) (Y2_4 List) (X1_4 List)) (=> (and (>= A_3 B_3) (<= A_4 (- B_4 1)) (append X_4 (mk-cons A_4 mk-nil) X1_4) (whl2 A_4 B_4 X1_4 Y_4 A2_4 B2_4 X2_4 Y2_4)) (all mk-nil 0 mk-nil 0 A_3 B_3 X_3 Y_3 A_3 B_3 X_3 Y_3 A_4 B_4 X_4 Y_4 A2_4 B2_4 X2_4 Y2_4))))
; all([], 0, [], 0, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
;     all([], 0, [], 0, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4),
;     A_3 =< B_3-1,
;     A1_3=A_3+1,
;     append(X_3, [A_3], X1_3),
;     append(Y_3, X_3, Y1_3),
;     A_4 >= B_4.
(assert (forall ((A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A2_3 Int) (B2_3 Int) (X2_3 List) (Y2_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List) (A1_3 Int) (X1_3 List) (Y1_3 List)) (=> (and (all mk-nil 0 mk-nil 0 A1_3 B_3 X1_3 Y1_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A_4 B_4 X_4 Y_4) (<= A_3 (- B_3 1)) (= A1_3 (+ A_3 1)) (append X_3 (mk-cons A_3 mk-nil) X1_3) (append Y_3 X_3 Y1_3) (>= A_4 B_4)) (all mk-nil 0 mk-nil 0 A_3 B_3 X_3 Y_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A_4 B_4 X_4 Y_4))))
; all([], 0, [], 0, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
;     all([], 0, [], 0, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4),
;     A_3 =< B_3-1,
;     A1_3=A_3+1,
;     append(X_3, [A_3], X1_3),
;     append(Y_3, X_3, Y1_3),
;     A_4 =< B_4-1,
;     append(X_4, [A_4], X1_4),
;     whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).
(assert (forall ((A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A2_3 Int) (B2_3 Int) (X2_3 List) (Y2_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List) (A2_4 Int) (B2_4 Int) (X2_4 List) (Y2_4 List) (A1_3 Int) (X1_3 List) (Y1_3 List) (X1_4 List)) (=> (and (all mk-nil 0 mk-nil 0 A1_3 B_3 X1_3 Y1_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A2_4 B2_4 X2_4 Y2_4) (<= A_3 (- B_3 1)) (= A1_3 (+ A_3 1)) (append X_3 (mk-cons A_3 mk-nil) X1_3) (append Y_3 X_3 Y1_3) (<= A_4 (- B_4 1)) (append X_4 (mk-cons A_4 mk-nil) X1_4) (whl2 A_4 B_4 X1_4 Y_4 A2_4 B2_4 X2_4 Y2_4)) (all mk-nil 0 mk-nil 0 A_3 B_3 X_3 Y_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A2_4 B2_4 X2_4 Y2_4))))
; all([], 0, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
;     sum_list(T1_2, S11_2),
;     S1_2 = H1_2 + S11_2,
;     A_3 >= B_3,
;     A_4 >= B_4.
(assert (forall ((H1_2 Int) (T1_2 List) (S1_2 Int) (A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List) (S11_2 Int)) (=> (and (sum_list T1_2 S11_2) (= S1_2 (+ H1_2 S11_2)) (>= A_3 B_3) (>= A_4 B_4)) (all mk-nil 0 (mk-cons H1_2 T1_2) S1_2 A_3 B_3 X_3 Y_3 A_3 B_3 X_3 Y_3 A_4 B_4 X_4 Y_4 A_4 B_4 X_4 Y_4))))
; all([], 0, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
;     sum_list(T1_2, S11_2),
;     S1_2 = H1_2 + S11_2,
;     A_3 >= B_3,
;     A_4 =< B_4-1,
;     append(X_4, [A_4], X1_4),
;     whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).
(assert (forall ((H1_2 Int) (T1_2 List) (S1_2 Int) (A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List) (A2_4 Int) (B2_4 Int) (X2_4 List) (Y2_4 List) (S11_2 Int) (X1_4 List)) (=> (and (sum_list T1_2 S11_2) (= S1_2 (+ H1_2 S11_2)) (>= A_3 B_3) (<= A_4 (- B_4 1)) (append X_4 (mk-cons A_4 mk-nil) X1_4) (whl2 A_4 B_4 X1_4 Y_4 A2_4 B2_4 X2_4 Y2_4)) (all mk-nil 0 (mk-cons H1_2 T1_2) S1_2 A_3 B_3 X_3 Y_3 A_3 B_3 X_3 Y_3 A_4 B_4 X_4 Y_4 A2_4 B2_4 X2_4 Y2_4))))
; all([], 0, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
;     all([], 0, [H1_2|T1_2], S1_2, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4),
;     sum_list(T1_2, S11_2),
;     S1_2 = H1_2 + S11_2,
;     A_3 =< B_3-1,
;     A1_3=A_3+1,
;     append(X_3, [A_3], X1_3),
;     append(Y_3, X_3, Y1_3),
;     A_4 >= B_4.
(assert (forall ((H1_2 Int) (T1_2 List) (S1_2 Int) (A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A2_3 Int) (B2_3 Int) (X2_3 List) (Y2_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List) (A1_3 Int) (X1_3 List) (Y1_3 List) (S11_2 Int)) (=> (and (all mk-nil 0 (mk-cons H1_2 T1_2) S1_2 A1_3 B_3 X1_3 Y1_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A_4 B_4 X_4 Y_4) (sum_list T1_2 S11_2) (= S1_2 (+ H1_2 S11_2)) (<= A_3 (- B_3 1)) (= A1_3 (+ A_3 1)) (append X_3 (mk-cons A_3 mk-nil) X1_3) (append Y_3 X_3 Y1_3) (>= A_4 B_4)) (all mk-nil 0 (mk-cons H1_2 T1_2) S1_2 A_3 B_3 X_3 Y_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A_4 B_4 X_4 Y_4))))
; all([], 0, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
;     all([], 0, [H1_2|T1_2], S1_2, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4),
;     sum_list(T1_2, S11_2),
;     S1_2 = H1_2 + S11_2,
;     A_3 =< B_3-1,
;     A1_3=A_3+1,
;     append(X_3, [A_3], X1_3),
;     append(Y_3, X_3, Y1_3),
;     A_4 =< B_4-1,
;     append(X_4, [A_4], X1_4),
;     whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).
(assert (forall ((H1_2 Int) (T1_2 List) (S1_2 Int) (A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A2_3 Int) (B2_3 Int) (X2_3 List) (Y2_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List) (A2_4 Int) (B2_4 Int) (X2_4 List) (Y2_4 List) (A1_3 Int) (X1_3 List) (Y1_3 List) (S11_2 Int) (X1_4 List)) (=> (and (all mk-nil 0 (mk-cons H1_2 T1_2) S1_2 A1_3 B_3 X1_3 Y1_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A2_4 B2_4 X2_4 Y2_4) (sum_list T1_2 S11_2) (= S1_2 (+ H1_2 S11_2)) (<= A_3 (- B_3 1)) (= A1_3 (+ A_3 1)) (append X_3 (mk-cons A_3 mk-nil) X1_3) (append Y_3 X_3 Y1_3) (<= A_4 (- B_4 1)) (append X_4 (mk-cons A_4 mk-nil) X1_4) (whl2 A_4 B_4 X1_4 Y_4 A2_4 B2_4 X2_4 Y2_4)) (all mk-nil 0 (mk-cons H1_2 T1_2) S1_2 A_3 B_3 X_3 Y_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A2_4 B2_4 X2_4 Y2_4))))
; all([H_1|T_1], S_1, [], 0, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
;     all(T_1, S1_1, [], 0, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4),
;     S_1 = H_1 + S1_1,
;     A_3 >= B_3,
;     A_4 >= B_4.
(assert (forall ((H_1 Int) (T_1 List) (S_1 Int) (A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List) (S1_1 Int)) (=> (and (all T_1 S1_1 mk-nil 0 A_3 B_3 X_3 Y_3 A_3 B_3 X_3 Y_3 A_4 B_4 X_4 Y_4 A_4 B_4 X_4 Y_4) (= S_1 (+ H_1 S1_1)) (>= A_3 B_3) (>= A_4 B_4)) (all (mk-cons H_1 T_1) S_1 mk-nil 0 A_3 B_3 X_3 Y_3 A_3 B_3 X_3 Y_3 A_4 B_4 X_4 Y_4 A_4 B_4 X_4 Y_4))))
; all([H_1|T_1], S_1, [], 0, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
;     all(T_1, S1_1, [], 0, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4),
;     S_1 = H_1 + S1_1,
;     A_3 >= B_3,
;     A_4 =< B_4-1,
;     append(X_4, [A_4], X1_4),
;     whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).
(assert (forall ((H_1 Int) (T_1 List) (S_1 Int) (A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List) (A2_4 Int) (B2_4 Int) (X2_4 List) (Y2_4 List) (S1_1 Int) (X1_4 List)) (=> (and (all T_1 S1_1 mk-nil 0 A_3 B_3 X_3 Y_3 A_3 B_3 X_3 Y_3 A_4 B_4 X_4 Y_4 A2_4 B2_4 X2_4 Y2_4) (= S_1 (+ H_1 S1_1)) (>= A_3 B_3) (<= A_4 (- B_4 1)) (append X_4 (mk-cons A_4 mk-nil) X1_4) (whl2 A_4 B_4 X1_4 Y_4 A2_4 B2_4 X2_4 Y2_4)) (all (mk-cons H_1 T_1) S_1 mk-nil 0 A_3 B_3 X_3 Y_3 A_3 B_3 X_3 Y_3 A_4 B_4 X_4 Y_4 A2_4 B2_4 X2_4 Y2_4))))
; all([H_1|T_1], S_1, [], 0, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
;     all(T_1, S1_1, [], 0, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4),
;     S_1 = H_1 + S1_1,
;     A_3 =< B_3-1,
;     A1_3=A_3+1,
;     append(X_3, [A_3], X1_3),
;     append(Y_3, X_3, Y1_3),
;     A_4 >= B_4.
(assert (forall ((H_1 Int) (T_1 List) (S_1 Int) (A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A2_3 Int) (B2_3 Int) (X2_3 List) (Y2_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List) (S1_1 Int) (A1_3 Int) (X1_3 List) (Y1_3 List)) (=> (and (all T_1 S1_1 mk-nil 0 A1_3 B_3 X1_3 Y1_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A_4 B_4 X_4 Y_4) (= S_1 (+ H_1 S1_1)) (<= A_3 (- B_3 1)) (= A1_3 (+ A_3 1)) (append X_3 (mk-cons A_3 mk-nil) X1_3) (append Y_3 X_3 Y1_3) (>= A_4 B_4)) (all (mk-cons H_1 T_1) S_1 mk-nil 0 A_3 B_3 X_3 Y_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A_4 B_4 X_4 Y_4))))
; all([H_1|T_1], S_1, [], 0, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
;     all(T_1, S1_1, [], 0, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4),
;     S_1 = H_1 + S1_1,
;     A_3 =< B_3-1,
;     A1_3=A_3+1,
;     append(X_3, [A_3], X1_3),
;     append(Y_3, X_3, Y1_3),
;     A_4 =< B_4-1,
;     append(X_4, [A_4], X1_4),
;     whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).
(assert (forall ((H_1 Int) (T_1 List) (S_1 Int) (A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A2_3 Int) (B2_3 Int) (X2_3 List) (Y2_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List) (A2_4 Int) (B2_4 Int) (X2_4 List) (Y2_4 List) (S1_1 Int) (A1_3 Int) (X1_3 List) (Y1_3 List) (X1_4 List)) (=> (and (all T_1 S1_1 mk-nil 0 A1_3 B_3 X1_3 Y1_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A2_4 B2_4 X2_4 Y2_4) (= S_1 (+ H_1 S1_1)) (<= A_3 (- B_3 1)) (= A1_3 (+ A_3 1)) (append X_3 (mk-cons A_3 mk-nil) X1_3) (append Y_3 X_3 Y1_3) (<= A_4 (- B_4 1)) (append X_4 (mk-cons A_4 mk-nil) X1_4) (whl2 A_4 B_4 X1_4 Y_4 A2_4 B2_4 X2_4 Y2_4)) (all (mk-cons H_1 T_1) S_1 mk-nil 0 A_3 B_3 X_3 Y_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A2_4 B2_4 X2_4 Y2_4))))
; all([H_1|T_1], S_1, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
;     all(T_1, S1_1, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4),
;     S_1 = H_1 + S1_1,
;     sum_list(T1_2, S11_2),
;     S1_2 = H1_2 + S11_2,
;     A_3 >= B_3,
;     A_4 >= B_4.
(assert (forall ((H_1 Int) (T_1 List) (S_1 Int) (H1_2 Int) (T1_2 List) (S1_2 Int) (A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List) (S1_1 Int) (S11_2 Int)) (=> (and (all T_1 S1_1 (mk-cons H1_2 T1_2) S1_2 A_3 B_3 X_3 Y_3 A_3 B_3 X_3 Y_3 A_4 B_4 X_4 Y_4 A_4 B_4 X_4 Y_4) (= S_1 (+ H_1 S1_1)) (sum_list T1_2 S11_2) (= S1_2 (+ H1_2 S11_2)) (>= A_3 B_3) (>= A_4 B_4)) (all (mk-cons H_1 T_1) S_1 (mk-cons H1_2 T1_2) S1_2 A_3 B_3 X_3 Y_3 A_3 B_3 X_3 Y_3 A_4 B_4 X_4 Y_4 A_4 B_4 X_4 Y_4))))
; all([H_1|T_1], S_1, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
;     all(T_1, S1_1, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A_3, B_3, X_3, Y_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4),
;     S_1 = H_1 + S1_1,
;     sum_list(T1_2, S11_2),
;     S1_2 = H1_2 + S11_2,
;     A_3 >= B_3,
;     A_4 =< B_4-1,
;     append(X_4, [A_4], X1_4),
;     whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).
(assert (forall ((H_1 Int) (T_1 List) (S_1 Int) (H1_2 Int) (T1_2 List) (S1_2 Int) (A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List) (A2_4 Int) (B2_4 Int) (X2_4 List) (Y2_4 List) (S1_1 Int) (S11_2 Int) (X1_4 List)) (=> (and (all T_1 S1_1 (mk-cons H1_2 T1_2) S1_2 A_3 B_3 X_3 Y_3 A_3 B_3 X_3 Y_3 A_4 B_4 X_4 Y_4 A2_4 B2_4 X2_4 Y2_4) (= S_1 (+ H_1 S1_1)) (sum_list T1_2 S11_2) (= S1_2 (+ H1_2 S11_2)) (>= A_3 B_3) (<= A_4 (- B_4 1)) (append X_4 (mk-cons A_4 mk-nil) X1_4) (whl2 A_4 B_4 X1_4 Y_4 A2_4 B2_4 X2_4 Y2_4)) (all (mk-cons H_1 T_1) S_1 (mk-cons H1_2 T1_2) S1_2 A_3 B_3 X_3 Y_3 A_3 B_3 X_3 Y_3 A_4 B_4 X_4 Y_4 A2_4 B2_4 X2_4 Y2_4))))
; all([H_1|T_1], S_1, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4) :-
;     all(T_1, S1_1, [H1_2|T1_2], S1_2, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A_4, B_4, X_4, Y_4),
;     S_1 = H_1 + S1_1,
;     sum_list(T1_2, S11_2),
;     S1_2 = H1_2 + S11_2,
;     A_3 =< B_3-1,
;     A1_3=A_3+1,
;     append(X_3, [A_3], X1_3),
;     append(Y_3, X_3, Y1_3),
;     A_4 >= B_4.
(assert (forall ((H_1 Int) (T_1 List) (S_1 Int) (H1_2 Int) (T1_2 List) (S1_2 Int) (A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A2_3 Int) (B2_3 Int) (X2_3 List) (Y2_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List) (S1_1 Int) (A1_3 Int) (X1_3 List) (Y1_3 List) (S11_2 Int)) (=> (and (all T_1 S1_1 (mk-cons H1_2 T1_2) S1_2 A1_3 B_3 X1_3 Y1_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A_4 B_4 X_4 Y_4) (= S_1 (+ H_1 S1_1)) (sum_list T1_2 S11_2) (= S1_2 (+ H1_2 S11_2)) (<= A_3 (- B_3 1)) (= A1_3 (+ A_3 1)) (append X_3 (mk-cons A_3 mk-nil) X1_3) (append Y_3 X_3 Y1_3) (>= A_4 B_4)) (all (mk-cons H_1 T_1) S_1 (mk-cons H1_2 T1_2) S1_2 A_3 B_3 X_3 Y_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A_4 B_4 X_4 Y_4))))
; all([H_1|T_1], S_1, [H1_2|T1_2], S1_2, A_3, B_3, X_3, Y_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4) :-
;     all(T_1, S1_1, [H1_2|T1_2], S1_2, A1_3, B_3, X1_3, Y1_3, A2_3, B2_3, X2_3, Y2_3, A_4, B_4, X_4, Y_4, A2_4, B2_4, X2_4, Y2_4),
;     S_1 = H_1 + S1_1,
;     sum_list(T1_2, S11_2),
;     S1_2 = H1_2 + S11_2,
;     A_3 =< B_3-1,
;     A1_3=A_3+1,
;     append(X_3, [A_3], X1_3),
;     append(Y_3, X_3, Y1_3),
;     A_4 =< B_4-1,
;     append(X_4, [A_4], X1_4),
;     whl2(A_4,B_4,X1_4,Y_4,A2_4,B2_4,X2_4,Y2_4).
(assert (forall ((H_1 Int) (T_1 List) (S_1 Int) (H1_2 Int) (T1_2 List) (S1_2 Int) (A_3 Int) (B_3 Int) (X_3 List) (Y_3 List) (A2_3 Int) (B2_3 Int) (X2_3 List) (Y2_3 List) (A_4 Int) (B_4 Int) (X_4 List) (Y_4 List) (A2_4 Int) (B2_4 Int) (X2_4 List) (Y2_4 List) (S1_1 Int) (A1_3 Int) (X1_3 List) (Y1_3 List) (S11_2 Int) (X1_4 List)) (=> (and (all T_1 S1_1 (mk-cons H1_2 T1_2) S1_2 A1_3 B_3 X1_3 Y1_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A2_4 B2_4 X2_4 Y2_4) (= S_1 (+ H_1 S1_1)) (sum_list T1_2 S11_2) (= S1_2 (+ H1_2 S11_2)) (<= A_3 (- B_3 1)) (= A1_3 (+ A_3 1)) (append X_3 (mk-cons A_3 mk-nil) X1_3) (append Y_3 X_3 Y1_3) (<= A_4 (- B_4 1)) (append X_4 (mk-cons A_4 mk-nil) X1_4) (whl2 A_4 B_4 X1_4 Y_4 A2_4 B2_4 X2_4 Y2_4)) (all (mk-cons H_1 T_1) S_1 (mk-cons H1_2 T1_2) S1_2 A_3 B_3 X_3 Y_3 A2_3 B2_3 X2_3 Y2_3 A_4 B_4 X_4 Y_4 A2_4 B2_4 X2_4 Y2_4))))
; append([], X, X).
(assert (forall ((X List)) (=> true (append mk-nil X X))))
; append([T|X], Y, [T|Z]) :- append(X, Y, Z).
(assert (forall ((T Int) (X List) (Y List) (Z List)) (=> (and (append X Y Z)) (append (mk-cons T X) Y (mk-cons T Z)))))
; whl1(A,B,X,Y,A,B,X,Y) :- A >= B.
(assert (forall ((A Int) (B Int) (X List) (Y List)) (=> (and (>= A B)) (whl1 A B X Y A B X Y))))
; whl1(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-1, A1=A+1, append(X, [A], X1), append(Y, X, Y1), whl1(A1,B,X1,Y1,A2,B2,X2,Y2).
(assert (forall ((A Int) (B Int) (X List) (Y List) (A2 Int) (B2 Int) (X2 List) (Y2 List) (A1 Int) (X1 List) (Y1 List)) (=> (and (<= A (- B 1)) (= A1 (+ A 1)) (append X (mk-cons A mk-nil) X1) (append Y X Y1) (whl1 A1 B X1 Y1 A2 B2 X2 Y2)) (whl1 A B X Y A2 B2 X2 Y2))))
; ifte(A,B,X,Y,A,B,X,Y ) :- A >= B.
(assert (forall ((A Int) (B Int) (X List) (Y List)) (=> (and (>= A B)) (ifte A B X Y A B X Y))))
; ifte(A,B,X,Y,A2,B2,X2,Y2) :- A =< B-1,
;     append(X, [A], X1), whl2(A,B,X1,Y,A2,B2,X2,Y2).
(assert (forall ((A Int) (B Int) (X List) (Y List) (A2 Int) (B2 Int) (X2 List) (Y2 List) (X1 List)) (=> (and (<= A (- B 1)) (append X (mk-cons A mk-nil) X1) (whl2 A B X1 Y A2 B2 X2 Y2)) (ifte A B X Y A2 B2 X2 Y2))))
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
; sum_list1([], 0).
(assert (=> true (sum_list1 mk-nil 0)))
; sum_list1([H1|T1], S1) :- sum_list(T1, S11), S1 = H1 + S11.
(assert (forall ((H1 Int) (T1 List) (S1 Int) (S11 Int)) (=> (and (sum_list T1 S11) (= S1 (+ H1 S11))) (sum_list1 (mk-cons H1 T1) S1))))
; ff1 :- ~(N1 = N2), all(X1, N1, X2, N2, A,B,X,Y,A1,B1,X1,Y1, A, B,X,Y,A2,B2,X2,Y2).
(assert (forall ((N1 Int) (N2 Int) (X1 List) (X2 List) (A Int) (B Int) (X List) (Y List) (A1 Int) (B1 Int) (Y1 List) (A2 Int) (B2 Int) (Y2 List)) (not (and (not (= N1 N2)) (all X1 N1 X2 N2 A B X Y A1 B1 X1 Y1 A B X Y A2 B2 X2 Y2)))))
(check-sat)