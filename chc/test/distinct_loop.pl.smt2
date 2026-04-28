(set-logic HORN)
(declare-datatypes () ((List (mk-nil) (mk-cons (head Int) (tail List)))))
(declare-fun loop (List Int) Bool)
(declare-fun loop1 (List Int) Bool)
(declare-fun start (Int) Bool)
; start(X).
(assert (forall ((X Int)) (=> true (start X))))
; loop([], X) :- constr(X = 0).
(assert (forall ((X Int)) (=> (and (= X 0)) (loop mk-nil X))))
; loop([Z|A0], J) :- constr(((J > 0) & (J0 = J - 1)) & (Z = 0)), loop(A0, J0).
(assert (forall ((Z Int) (A0 List) (J Int) (J0 Int)) (=> (and (and (and (> J 0) (= J0 (- J 1))) (= Z 0)) (loop A0 J0)) (loop (mk-cons Z A0) J))))
; loop1([], X1) :- constr(X1 = 0).
(assert (forall ((X1 Int)) (=> (and (= X1 0)) (loop1 mk-nil X1))))
; loop1([Z1|A01], J1) :- constr(((J1 > 0) & (J01 = J1 - 1)) & (Z1 = 0)), loop1(A01, J01).
(assert (forall ((Z1 Int) (A01 List) (J1 Int) (J01 Int)) (=> (and (and (and (> J1 0) (= J01 (- J1 1))) (= Z1 0)) (loop1 A01 J01)) (loop1 (mk-cons Z1 A01) J1))))
; ff1 :- start(X), loop(A1, N), loop(A2, M), constr(((N = 2) & (M = 100)) & (A1 = A2)).
(assert (forall ((X Int) (A1 List) (N Int) (A2 List) (M Int)) (not (and (start X) (loop A1 N) (loop A2 M) (and (and (= N 2) (= M 100)) (= A1 A2))))))
(check-sat)