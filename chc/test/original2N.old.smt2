(set-logic HORN)
(set-option :produce-models true)
(declare-datatypes ((Lst_0 0)) (((cons_0  (head_0 Int) (tail_0 Lst_0)) (nil_0 ))))
(declare-fun |append_0| ( Lst_0 Lst_0 Lst_0 ) Bool)
(declare-fun |length_0| ( Lst_0 Int ) Bool)
(declare-fun |loop1|( Lst_0 Lst_0 Int Int ) Bool)
(declare-fun |loop2|( Lst_0 Int ) Bool)
(declare-fun |loop3|( Lst_0 Int ) Bool)
(declare-const N Int)
; append_0 nil_0 A A
(assert
  (forall ((A Lst_0)) 
    (append_0 nil_0 A A)
  )
)
; (append_0 (cons_0 T X) Y (cons_0 T Z)) <- (append_0 X Y Z)
(assert 
    (forall ((T Int) (X Lst_0) (Y Lst_0) (Z Lst_0) (Tx Lst_0) (Tz Lst_0))
        (=>
            (and
                (append_0 X Y Z)
                (= Tx (cons_0 T X))
                (= Tz (cons_0 T Z))
            )
            (append_0 Tx Y Tz)
        )   
    )
)
; length_0 nil_0 0
(assert
    (length_0 nil_0 0)
)
; Len([T|X], N) <- Len(X, N0), N = N0 + 1
(assert
  (forall ( (Tx Lst_0) (X Lst_0) (N Int) (T Int) (N0 Int)) 
    (=>
      (and
        (length_0 X N0) 
        (= Tx (cons_0 T X)) 
        (= N (+ N0 1))
      )
      (length_0 Tx N)
    )
  )
)
; Loop1([], [], 0) <- True
(assert
    (forall ((N0 Int))
        (loop1 nil_0 nil_0 0 N0)
    )
)
; loop1(A, B, I, N0) :- I > 0, I0 is I - 1, loop2(A1, N0), loop3(B1, I), loop1(A0, B0, I0, N0), append(A1, A0, A), append(B1, B0, B).
(assert
    (forall ((A1 Lst_0) (A0 Lst_0) (B1 Lst_0) (B0 Lst_0) (A Lst_0) (B Lst_0) (i Int) (i0 Int) (N0 Int))
        (=>
            (and 
                (> i 0)
                (loop2 A1 N0)
                (loop3 B1 i)
                (loop1 A0 B0 i0 N0)
                (append_0 A1 A0 A)
                (append_0 B1 B0 B)
                (= i (+ i0 1))
            )
            (loop1 A B i N0)
        )
    )
)
; loop2([], 0).
(assert
    (loop2 nil_0 0)
)

; loop2(A, J) :- J > 0, J0 is J - 1, loop2(A0, J0), append(A0, [0], A).
(assert
    (forall ((A0 Lst_0) (A Lst_0) (J Int) (J0 Int))
        (=>
            (and 
                (loop2 A0 J0)
                (append_0 A0 (cons_0 0 nil_0) A)
                (> J 0)
                (= J (+ J0 1))
            )
            (loop2 A J)
        )
    )
)

; loop3([], 0).
(assert
    (loop3 nil_0 0)
)

; loop3(B, J) :- J > 0, J0 is J - 1, loop3(B0, J0), append(B0, [0], B).
(assert
    (forall ((B0 Lst_0) (B Lst_0) (J Int) (J0 Int))
        (=>
            (and 
                (loop3 B0 J0)
                (append_0 B0 (cons_0 0 nil_0) B)
                (> J 0)
                (= J (+ J0 1))
            )
            (loop3 B J)
        )
    )
)
(assert
    (forall ((A Lst_0) (B Lst_0) (Na Int) (Nb Int) (N0 Int))  
        (=>
            (and
                (> N0 0)
                (loop1 A B N0 N0)
                (length_0 A Na)
                (length_0 B Nb)
                (< Na Nb)
            )
            false
        )
    )
)
(check-sat)
; (get-model)
(exit)
