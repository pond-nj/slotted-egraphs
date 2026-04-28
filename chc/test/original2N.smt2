(set-logic HORN)
(declare-datatypes () ((List (mk-nil) (mk-cons (head Int) (tail List)))))
(declare-fun append (List List List) Bool)
(declare-fun len (List Int) Bool)
(declare-fun loop1 (List List Int Int) Bool)
(declare-fun loop2 (List Int) Bool)
(declare-fun loop3 (List Int) Bool)
; append([], X, X).
(assert (forall ((X List)) (=> true (append mk-nil X X))))
; append([T|X], Y, [T|Z]) :- append(X, Y, Z).
(assert (forall ((T Int) (X List) (Y List) (Z List)) (=> (and (append X Y Z)) (append (mk-cons T X) Y (mk-cons T Z)))))
; len([], X) :- X = 0.
(assert (forall ((X Int)) (=> (and (= X 0)) (len mk-nil X))))
; len([T|X], N) :- len(X, N0), N = N0 + 1.
(assert (forall ((T Int) (X List) (N Int) (N0 Int)) (=> (and (len X N0) (= N (+ N0 1))) (len (mk-cons T X) N))))
; loop1([], [], X, _) :- X = 0.
(assert (forall ((X Int) (Z Int)) (=> (and (= X 0)) (loop1 mk-nil mk-nil X Z))))
; loop1(A, B, I, N) :- I > 0, I0 = I - 1, loop2(A1, N), loop3(B1, I),
;     loop1(A0, B0, I0, N), append(A1, A0, A), append(B1, B0, B).
(assert (forall ((A List) (B List) (I Int) (N Int) (I0 Int) (A1 List) (B1 List) (A0 List) (B0 List)) (=> (and (> I 0) (= I0 (- I 1)) (loop2 A1 N) (loop3 B1 I) (loop1 A0 B0 I0 N) (append A1 A0 A) (append B1 B0 B)) (loop1 A B I N))))
; loop2([], X) :- X = 0.
(assert (forall ((X Int)) (=> (and (= X 0)) (loop2 mk-nil X))))
; loop2(A, J) :- J > 0, J0 = J - 1, loop2(A0, J0), append(A0, [Z], A), Z = 0.
(assert (forall ((A List) (J Int) (J0 Int) (A0 List) (Z Int)) (=> (and (> J 0) (= J0 (- J 1)) (loop2 A0 J0) (append A0 (mk-cons Z mk-nil) A) (= Z 0)) (loop2 A J))))
; loop3([], X) :- X = 0.
(assert (forall ((X Int)) (=> (and (= X 0)) (loop3 mk-nil X))))
; loop3(B, J) :- J > 0, J0 = J - 1, loop3(B0, J0), append(B0, [Z], B), Z = 0.
(assert (forall ((B List) (J Int) (J0 Int) (B0 List) (Z Int)) (=> (and (> J 0) (= J0 (- J 1)) (loop3 B0 J0) (append B0 (mk-cons Z mk-nil) B) (= Z 0)) (loop3 B J))))
; incorrect :- loop1(A, B, X, Y), len(A, Na), len(B, Nb), Na < Nb, Y > 0, X = Y.
(assert (forall ((A List) (B List) (X Int) (Y Int) (Na Int) (Nb Int)) (not (and (loop1 A B X Y) (len A Na) (len B Nb) (< Na Nb) (> Y 0) (= X Y)))))
(check-sat)