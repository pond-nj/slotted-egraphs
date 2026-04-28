(set-logic HORN)
(declare-datatypes () ((List (mk-nil) (mk-cons (head Int) (tail List)))))
(declare-fun new3 (Bool Int Bool Bool Int Bool) Bool)
(declare-fun new37 (Bool Int Bool Bool Int Bool Bool Int Bool Int Bool Bool Int Bool Int Int Bool) Bool)
(declare-fun new7 (Bool Int Bool Int Bool Bool Int Bool Int Int Bool) Bool)
; new37(A_1, B_1, C_1, D_1, E_1, F_1, A_2, B_2, C_2, D_2, E_2, F_2, G_2, H_2, D_2, I_2, J_2) :-
;     (A_1),
;     (C_1),
;     not(D_1), E_1=0,
;     (F_1),
;     A_2, B_2=D_2,
;     (C_2=(K_2=>(D_2>=L_2&M_2))),
;     (E_2),
;     ~F_2, G_2=0,
;     (H_2),
;     (J_2=(I_2=<D_2&N_2)),
;     (M_2),
;     ~K_2, L_2=0, 
;     (N_2).
(assert (forall ((A_1 Bool) (B_1 Int) (C_1 Bool) (D_1 Bool) (E_1 Int) (F_1 Bool) (A_2 Bool) (B_2 Int) (C_2 Bool) (D_2 Int) (E_2 Bool) (F_2 Bool) (G_2 Int) (H_2 Bool) (I_2 Int) (J_2 Bool) (K_2 Bool) (L_2 Int) (M_2 Bool) (N_2 Bool)) (=> (and A_1 C_1 (not D_1) (= E_1 0) F_1 A_2 (= B_2 D_2) (= C_2 (=> K_2 (and (>= D_2 L_2) M_2))) E_2 (not F_2) (= G_2 0) H_2 (= J_2 (and (<= I_2 D_2) N_2)) M_2 (not K_2) (= L_2 0) N_2) (new37 A_1 B_1 C_1 D_1 E_1 F_1 A_2 B_2 C_2 D_2 E_2 F_2 G_2 H_2 D_2 I_2 J_2))))
; new37(A_1, B_1, C_1, D_1, E_1, F_1, A_2, B_2, C_2, D_2, E_2, F_2, G_2, H_2, D_2, I_2, J_2) :-
;     new37(A_1, B_1, C_1, D_1, E_1, F_1, L_2, M_2, N_2, D_2, O_2, P_2, Q_2, R_2, D_2, I_2, S_2),
;     (A_1),
;     (C_1),
;     (~D_1&E_1=0),
;     (F_1),
;     (A_2&B_2=K_2),
;     (C_2=(L_2=>(K_2>=M_2&N_2))),
;     (E_2=(D_2=<K_2&O_2)),
;     (F_2&G_2=K_2),
;     (H_2=(P_2=>(K_2>=Q_2&R_2))),
;     (J_2=(I_2=<K_2&S_2)),
;     (O_2=>R_2=N_2).
(assert (forall ((A_1 Bool) (B_1 Int) (C_1 Bool) (D_1 Bool) (E_1 Int) (F_1 Bool) (A_2 Bool) (B_2 Int) (C_2 Bool) (D_2 Int) (E_2 Bool) (F_2 Bool) (G_2 Int) (H_2 Bool) (I_2 Int) (J_2 Bool) (L_2 Bool) (M_2 Int) (N_2 Bool) (O_2 Bool) (P_2 Bool) (Q_2 Int) (R_2 Bool) (S_2 Bool) (K_2 Int)) (=> (and (new37 A_1 B_1 C_1 D_1 E_1 F_1 L_2 M_2 N_2 D_2 O_2 P_2 Q_2 R_2 D_2 I_2 S_2) A_1 C_1 (and (not D_1) (= E_1 0)) F_1 (and A_2 (= B_2 K_2)) (= C_2 (=> L_2 (and (>= K_2 M_2) N_2))) (= E_2 (and (<= D_2 K_2) O_2)) (and F_2 (= G_2 K_2)) (= H_2 (=> P_2 (and (>= K_2 Q_2) R_2))) (= J_2 (and (<= I_2 K_2) S_2)) (=> O_2 (= R_2 N_2))) (new37 A_1 B_1 C_1 D_1 E_1 F_1 A_2 B_2 C_2 D_2 E_2 F_2 G_2 H_2 D_2 I_2 J_2))))
; new37(A_1, B_1, C_1, D_1, E_1, F_1, A_2, B_2, C_2, D_2, E_2, F_2, G_2, H_2, D_2, I_2, J_2) :-
;     new37(K_1, G_1, L_1, H_1, I_1, J_1, A_2, B_2, C_2, D_2, E_2, F_2, G_2, H_2, D_2, I_2, J_2),
;     (D_1&E_1=G_1),
;     (F_1=(H_1=>(G_1=<I_1&J_1))),
;     (J_1=K_1),
;     (L_1=>K_1=A_1),
;     new7(M_1,N_1,A_1,G_1,L_1,O_1,P_1,K_1,G_1,B_1,C_1),
;     (A_2&B_2=D_2),
;     (C_2=(K_2=>(D_2>=L_2&M_2))),
;     (E_2),
;     (~F_2&G_2=0),
;     (H_2),
;     (J_2=(I_2=<D_2&N_2)),
;     (M_2),
;     (~K_2&L_2=0),
;     (N_2).
(assert (forall ((A_1 Bool) (B_1 Int) (C_1 Bool) (D_1 Bool) (E_1 Int) (F_1 Bool) (A_2 Bool) (B_2 Int) (C_2 Bool) (D_2 Int) (E_2 Bool) (F_2 Bool) (G_2 Int) (H_2 Bool) (I_2 Int) (J_2 Bool) (K_1 Bool) (G_1 Int) (L_1 Bool) (H_1 Bool) (I_1 Int) (J_1 Bool) (M_1 Bool) (N_1 Int) (O_1 Bool) (P_1 Int) (K_2 Bool) (L_2 Int) (M_2 Bool) (N_2 Bool)) (=> (and (new37 K_1 G_1 L_1 H_1 I_1 J_1 A_2 B_2 C_2 D_2 E_2 F_2 G_2 H_2 D_2 I_2 J_2) (and D_1 (= E_1 G_1)) (= F_1 (=> H_1 (and (<= G_1 I_1) J_1))) (= J_1 K_1) (=> L_1 (= K_1 A_1)) (new7 M_1 N_1 A_1 G_1 L_1 O_1 P_1 K_1 G_1 B_1 C_1) (and A_2 (= B_2 D_2)) (= C_2 (=> K_2 (and (>= D_2 L_2) M_2))) E_2 (and (not F_2) (= G_2 0)) H_2 (= J_2 (and (<= I_2 D_2) N_2)) M_2 (and (not K_2) (= L_2 0)) N_2) (new37 A_1 B_1 C_1 D_1 E_1 F_1 A_2 B_2 C_2 D_2 E_2 F_2 G_2 H_2 D_2 I_2 J_2))))
; new37(A_1, B_1, C_1, D_1, E_1, F_1, A_2, B_2, C_2, D_2, E_2, F_2, G_2, H_2, D_2, I_2, J_2) :-
;     new37(K_1, G_1, L_1, H_1, I_1, J_1, L_2, M_2, N_2, D_2, O_2, P_2, Q_2, R_2, D_2, I_2, S_2),
;     (D_1&E_1=G_1),
;     (F_1=(H_1=>(G_1=<I_1&J_1))),
;     (J_1=K_1),
;     (L_1=>K_1=A_1),
;     new7(M_1,N_1,A_1,G_1,L_1,O_1,P_1,K_1,G_1,B_1,C_1),
;     (A_2&B_2=K_2),
;     (C_2=(L_2=>(K_2>=M_2&N_2))),
;     (E_2=(D_2=<K_2&O_2)),
;     (F_2&G_2=K_2),
;     (H_2=(P_2=>(K_2>=Q_2&R_2))),
;     (J_2=(I_2=<K_2&S_2)),
;     (O_2=>R_2=N_2).
(assert (forall ((A_1 Bool) (B_1 Int) (C_1 Bool) (D_1 Bool) (E_1 Int) (F_1 Bool) (A_2 Bool) (B_2 Int) (C_2 Bool) (D_2 Int) (E_2 Bool) (F_2 Bool) (G_2 Int) (H_2 Bool) (I_2 Int) (J_2 Bool) (K_1 Bool) (G_1 Int) (L_1 Bool) (H_1 Bool) (I_1 Int) (J_1 Bool) (L_2 Bool) (M_2 Int) (N_2 Bool) (O_2 Bool) (P_2 Bool) (Q_2 Int) (R_2 Bool) (S_2 Bool) (M_1 Bool) (N_1 Int) (O_1 Bool) (P_1 Int) (K_2 Int)) (=> (and (new37 K_1 G_1 L_1 H_1 I_1 J_1 L_2 M_2 N_2 D_2 O_2 P_2 Q_2 R_2 D_2 I_2 S_2) (and D_1 (= E_1 G_1)) (= F_1 (=> H_1 (and (<= G_1 I_1) J_1))) (= J_1 K_1) (=> L_1 (= K_1 A_1)) (new7 M_1 N_1 A_1 G_1 L_1 O_1 P_1 K_1 G_1 B_1 C_1) (and A_2 (= B_2 K_2)) (= C_2 (=> L_2 (and (>= K_2 M_2) N_2))) (= E_2 (and (<= D_2 K_2) O_2)) (and F_2 (= G_2 K_2)) (= H_2 (=> P_2 (and (>= K_2 Q_2) R_2))) (= J_2 (and (<= I_2 K_2) S_2)) (=> O_2 (= R_2 N_2))) (new37 A_1 B_1 C_1 D_1 E_1 F_1 A_2 B_2 C_2 D_2 E_2 F_2 G_2 H_2 D_2 I_2 J_2))))
; new7(A,B,C,D,E,F,G,H,D,I,J) :- (A&B=D), (C=(K=>(D>=L&M))), (E), (~F&G=0), (H),
;           (J=(I=<D&N)), (M), (~K&L=0), (N).
(assert (forall ((A Bool) (B Int) (C Bool) (D Int) (E Bool) (F Bool) (G Int) (H Bool) (I Int) (J Bool) (K Bool) (L Int) (M Bool) (N Bool)) (=> (and (and A (= B D)) (= C (=> K (and (>= D L) M))) E (and (not F) (= G 0)) H (= J (and (<= I D) N)) M (and (not K) (= L 0)) N) (new7 A B C D E F G H D I J))))
; new7(A,B,C,D,E,F,G,H,D,I,J) :- (A&B=K), (C=(L=>(K>=M&N))), (E=(D=<K&O)),
;           (F&G=K), (H=(P=>(K>=Q&R))), (J=(I=<K&S)), (O=>R=N),
;           new7(L,M,N,D,O,P,Q,R,D,I,S).
(assert (forall ((A Bool) (B Int) (C Bool) (D Int) (E Bool) (F Bool) (G Int) (H Bool) (I Int) (J Bool) (K Int) (L Bool) (M Int) (N Bool) (O Bool) (P Bool) (Q Int) (R Bool) (S Bool)) (=> (and (and A (= B K)) (= C (=> L (and (>= K M) N))) (= E (and (<= D K) O)) (and F (= G K)) (= H (=> P (and (>= K Q) R))) (= J (and (<= I K) S)) (=> O (= R N)) (new7 L M N D O P Q R D I S)) (new7 A B C D E F G H D I J))))
; new3(A,B,C,D,E,F) :- (A), (C), (~D&E=0), (F).
(assert (forall ((A Bool) (B Int) (C Bool) (D Bool) (E Int) (F Bool)) (=> (and A C (and (not D) (= E 0)) F) (new3 A B C D E F))))
; new3(A,B,C,D,E,F) :- (D&E=G), (F=(H=>(G=<I&J))), (J=K), (L=>K=A),
;           new37(K,G,L,H,I,J, M,N,A,G,L,O,P,K,G,B,C),.
(assert (forall ((A Bool) (B Int) (C Bool) (D Bool) (E Int) (F Bool) (G Int) (H Bool) (I Int) (J Bool) (K Bool) (L Bool) (M Bool) (N Int) (O Bool) (P Int)) (=> (and (and D (= E G)) (= F (=> H (and (<= G I) J))) (= J K) (=> L (= K A)) (new37 K G L H I J M N A G L O P K G B C)) (new3 A B C D E F))))
; ff1 :- (A& ~B), new3(B,C,D,E,F,A).
(assert (forall ((A Bool) (B Bool) (C Int) (D Bool) (E Bool) (F Int)) (not (and (and A (not B)) (new3 B C D E F A)))))
(check-sat)