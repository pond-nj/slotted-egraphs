(set-logic HORN)
(declare-datatypes () ((List (mk-nil) (mk-cons (head Int) (tail List)))))
(declare-fun hd (List Bool Int) Bool)
(declare-fun new (List Bool List Bool List List) Bool)
(declare-fun snoc (List Int List) Bool)
; new([], Res_1, [], Res_2, [], []) :-
;     constr(Res_1),
;     constr(Res_2).
(assert (forall ((Res_1 Bool) (Res_2 Bool)) (=> (and Res_1 Res_2) (new mk-nil Res_1 mk-nil Res_2 mk-nil mk-nil))))
; new([], Res_1, [], Res_2, [H_3|T_3], R_3) :-
;     new([], Res_1, [], Res_2, T_3, S_3),
;     constr(Res_1),
;     constr(Res_2),
;     snoc(S_3, H_3, R_3).
(assert (forall ((Res_1 Bool) (Res_2 Bool) (H_3 Int) (T_3 List) (R_3 List) (S_3 List)) (=> (and (new mk-nil Res_1 mk-nil Res_2 T_3 S_3) Res_1 Res_2 (snoc S_3 H_3 R_3)) (new mk-nil Res_1 mk-nil Res_2 (mk-cons H_3 T_3) R_3))))
; new([], Res_1, [H_2|T_2], Res_2, [], []) :-
;     new([], Res_1, T_2, ResT_2, [], []),
;     constr(Res_1),
;     hd(T_2, IsDefT_2, HdT_2),
;     constr(Res_2 = (IsDefT_2 => ((H_2 >= HdT_2) & ResT_2))).
(assert (forall ((Res_1 Bool) (H_2 Int) (T_2 List) (Res_2 Bool) (ResT_2 Bool) (IsDefT_2 Bool) (HdT_2 Int)) (=> (and (new mk-nil Res_1 T_2 ResT_2 mk-nil mk-nil) Res_1 (hd T_2 IsDefT_2 HdT_2) (= Res_2 (=> IsDefT_2 (and (>= H_2 HdT_2) ResT_2)))) (new mk-nil Res_1 (mk-cons H_2 T_2) Res_2 mk-nil mk-nil))))
; new([], Res_1, [H_2|T_2], Res_2, [H_3|T_3], R_3) :-
;     new([], Res_1, T_2, ResT_2, T_3, S_3),
;     constr(Res_1),
;     hd(T_2, IsDefT_2, HdT_2),
;     constr(Res_2 = (IsDefT_2 => ((H_2 >= HdT_2) & ResT_2))),
;     snoc(S_3, H_3, R_3).
(assert (forall ((Res_1 Bool) (H_2 Int) (T_2 List) (Res_2 Bool) (H_3 Int) (T_3 List) (R_3 List) (ResT_2 Bool) (S_3 List) (IsDefT_2 Bool) (HdT_2 Int)) (=> (and (new mk-nil Res_1 T_2 ResT_2 T_3 S_3) Res_1 (hd T_2 IsDefT_2 HdT_2) (= Res_2 (=> IsDefT_2 (and (>= H_2 HdT_2) ResT_2))) (snoc S_3 H_3 R_3)) (new mk-nil Res_1 (mk-cons H_2 T_2) Res_2 (mk-cons H_3 T_3) R_3))))
; new([H_1|T_1], Res_1, [], Res_2, [], []) :-
;     new(T_1, ResT_1, [], Res_2, [], []),
;     hd(T_1, IsDefT_1, HdT_1),
;     constr(Res_1 = (IsDefT_1 => ((H_1 =< HdT_1) & ResT_1))),
;     constr(Res_2).
(assert (forall ((H_1 Int) (T_1 List) (Res_1 Bool) (Res_2 Bool) (ResT_1 Bool) (IsDefT_1 Bool) (HdT_1 Int)) (=> (and (new T_1 ResT_1 mk-nil Res_2 mk-nil mk-nil) (hd T_1 IsDefT_1 HdT_1) (= Res_1 (=> IsDefT_1 (and (<= H_1 HdT_1) ResT_1))) Res_2) (new (mk-cons H_1 T_1) Res_1 mk-nil Res_2 mk-nil mk-nil))))
; new([H_1|T_1], Res_1, [], Res_2, [H_3|T_3], R_3) :-
;     new(T_1, ResT_1, [], Res_2, T_3, S_3),
;     hd(T_1, IsDefT_1, HdT_1),
;     constr(Res_1 = (IsDefT_1 => ((H_1 =< HdT_1) & ResT_1))),
;     constr(Res_2),
;     snoc(S_3, H_3, R_3).
(assert (forall ((H_1 Int) (T_1 List) (Res_1 Bool) (Res_2 Bool) (H_3 Int) (T_3 List) (R_3 List) (ResT_1 Bool) (S_3 List) (IsDefT_1 Bool) (HdT_1 Int)) (=> (and (new T_1 ResT_1 mk-nil Res_2 T_3 S_3) (hd T_1 IsDefT_1 HdT_1) (= Res_1 (=> IsDefT_1 (and (<= H_1 HdT_1) ResT_1))) Res_2 (snoc S_3 H_3 R_3)) (new (mk-cons H_1 T_1) Res_1 mk-nil Res_2 (mk-cons H_3 T_3) R_3))))
; new([H_1|T_1], Res_1, [H_2|T_2], Res_2, [], []) :-
;     new(T_1, ResT_1, T_2, ResT_2, [], []),
;     hd(T_1, IsDefT_1, HdT_1),
;     constr(Res_1 = (IsDefT_1 => ((H_1 =< HdT_1) & ResT_1))),
;     hd(T_2, IsDefT_2, HdT_2),
;     constr(Res_2 = (IsDefT_2 => ((H_2 >= HdT_2) & ResT_2))).
(assert (forall ((H_1 Int) (T_1 List) (Res_1 Bool) (H_2 Int) (T_2 List) (Res_2 Bool) (ResT_1 Bool) (ResT_2 Bool) (IsDefT_1 Bool) (HdT_1 Int) (IsDefT_2 Bool) (HdT_2 Int)) (=> (and (new T_1 ResT_1 T_2 ResT_2 mk-nil mk-nil) (hd T_1 IsDefT_1 HdT_1) (= Res_1 (=> IsDefT_1 (and (<= H_1 HdT_1) ResT_1))) (hd T_2 IsDefT_2 HdT_2) (= Res_2 (=> IsDefT_2 (and (>= H_2 HdT_2) ResT_2)))) (new (mk-cons H_1 T_1) Res_1 (mk-cons H_2 T_2) Res_2 mk-nil mk-nil))))
; new([H_1|T_1], Res_1, [H_2|T_2], Res_2, [H_3|T_3], R_3) :-
;     new(T_1, ResT_1, T_2, ResT_2, T_3, S_3),
;     hd(T_1, IsDefT_1, HdT_1),
;     constr(Res_1 = (IsDefT_1 => ((H_1 =< HdT_1) & ResT_1))),
;     hd(T_2, IsDefT_2, HdT_2),
;     constr(Res_2 = (IsDefT_2 => ((H_2 >= HdT_2) & ResT_2))),
;     snoc(S_3, H_3, R_3).
(assert (forall ((H_1 Int) (T_1 List) (Res_1 Bool) (H_2 Int) (T_2 List) (Res_2 Bool) (H_3 Int) (T_3 List) (R_3 List) (ResT_1 Bool) (ResT_2 Bool) (S_3 List) (IsDefT_1 Bool) (HdT_1 Int) (IsDefT_2 Bool) (HdT_2 Int)) (=> (and (new T_1 ResT_1 T_2 ResT_2 T_3 S_3) (hd T_1 IsDefT_1 HdT_1) (= Res_1 (=> IsDefT_1 (and (<= H_1 HdT_1) ResT_1))) (hd T_2 IsDefT_2 HdT_2) (= Res_2 (=> IsDefT_2 (and (>= H_2 HdT_2) ResT_2))) (snoc S_3 H_3 R_3)) (new (mk-cons H_1 T_1) Res_1 (mk-cons H_2 T_2) Res_2 (mk-cons H_3 T_3) R_3))))
; snoc([], X, [X]).
(assert (forall ((X Int)) (=> true (snoc mk-nil X (mk-cons X mk-nil)))))
; snoc([X|Xs], Y, [X|Zs]) :- snoc(Xs, Y, Zs).
(assert (forall ((X Int) (Xs List) (Y Int) (Zs List)) (=> (and (snoc Xs Y Zs)) (snoc (mk-cons X Xs) Y (mk-cons X Zs)))))
; hd([], IsDef, Hd)    :- constr((~IsDef) & (Hd = 0)).
(assert (forall ((IsDef Bool) (Hd Int)) (=> (and (and (not IsDef) (= Hd 0))) (hd mk-nil IsDef Hd))))
; hd([H|T], IsDef, Hd) :- constr(IsDef & (Hd = H)).
(assert (forall ((H Int) (T List) (IsDef Bool) (Hd Int)) (=> (and (and IsDef (= Hd H))) (hd (mk-cons H T) IsDef Hd))))
; ff1 :-
;     constr(BL & (~BR)),
;     new(L, BL, R, BR, L, R).
(assert (forall ((BL Bool) (BR Bool) (L List) (R List)) (not (and (and BL (not BR)) (new L BL R BR L R)))))
(check-sat)