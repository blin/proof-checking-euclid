Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Par.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_def_SameSide.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_collinear2.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_flip.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_rotate.
Require Import ProofCheckingEuclid.by_prop_SameSide_flip.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Playfair.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_diagonalsbisect.
Require Import ProofCheckingEuclid.lemma_diagonalsmeet.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_parallelbetween.
Require Import ProofCheckingEuclid.lemma_samesidecollinear.
Require Import ProofCheckingEuclid.lemma_samesidetransitive.
Require Import ProofCheckingEuclid.lemma_triangletoparallelogram.
Require Import ProofCheckingEuclid.proposition_15.
Require Import ProofCheckingEuclid.proposition_30.
Require Import ProofCheckingEuclid.proposition_31.
Require Import ProofCheckingEuclid.proposition_33B.
Require Import ProofCheckingEuclid.proposition_34.
Require Import ProofCheckingEuclid.proposition_43.
Require Import ProofCheckingEuclid.proposition_43B.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_44A :
	forall A B D E F G J N,
	Parallelogram B E F G ->
	CongA E B G J D N ->
	BetS A B E ->
	exists X Y, Parallelogram A B X Y /\ CongA A B X J D N /\ EqAreaQuad B E F G Y X B A /\ BetS G B X.
Proof.
	intros A B D E F G J N.
	intros Parallelogram_B_E_F_G.
	intros CongA_E_B_G_J_D_N.
	intros BetS_A_B_E.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq E E) as eq_E_E by (reflexivity).
	assert (eq F F) as eq_F_F by (reflexivity).
	assert (eq G G) as eq_G_G by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C G B G eq_G_G) as Col_G_B_G.
	pose proof (by_def_Col_from_eq_B_C A B B eq_B_B) as Col_A_B_B.
	pose proof (by_def_Col_from_eq_B_C B E E eq_E_E) as Col_B_E_E.
	pose proof (by_def_Col_from_eq_B_C E B B eq_B_B) as Col_E_B_B.
	pose proof (by_def_Col_from_eq_B_C F E E eq_E_E) as Col_F_E_E.
	pose proof (by_def_Col_from_eq_B_C G B B eq_B_B) as Col_G_B_B.
	pose proof (by_def_Col_from_eq_B_C G F F eq_F_F) as Col_G_F_F.

	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_B_E_F_G) as Parallelogram_E_F_G_B.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_E_F_G_B) as Parallelogram_F_G_B_E.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_F_G_B_E) as Parallelogram_G_B_E_F.

	pose proof (proposition_34 _ _ _ _ Parallelogram_G_B_E_F) as (_ & Cong_G_B_F_E & _ & _ & _).

	assert (Parallelogram_G_B_E_F_2 := Parallelogram_G_B_E_F).
	destruct Parallelogram_G_B_E_F_2 as (Par_G_B_E_F & Par_G_F_B_E).

	pose proof (by_prop_Par_flip _ _ _ _ Par_G_B_E_F) as (_ & Par_G_B_F_E & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_G_B_F_E) as Par_F_E_G_B.

	pose proof (by_prop_Par_flip _ _ _ _ Par_G_F_B_E) as (_ & Par_G_F_E_B & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_G_F_B_E) as Par_B_E_G_F.
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_B_E_G_F) as TarskiPar_B_E_G_F.
	pose proof (by_prop_Par_NC _ _ _ _ Par_G_F_E_B) as (_ & _ & nCol_F_E_B & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_F_E_B) as (neq_F_E & _ & _ & _ & _ & _).

	pose proof (by_prop_Par_NC _ _ _ _ Par_G_F_B_E) as (_ & nCol_G_B_E & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_G_B_E) as (_ & _ & _ & _ & nCol_E_B_G).
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_G_B_E) as CongA_G_B_E_E_B_G.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_G_B_E) as (neq_G_B & _ & _ & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_E_B_G) as (_ & neq_B_G & _ & _ & _ & _).
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_E) as BetS_E_B_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_B_E) as (neq_B_E & neq_A_B & neq_A_E).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_B_A) as (neq_B_A & neq_E_B & neq_E_A).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_B_E) as Col_A_B_E.
	pose proof (by_prop_Col_order _ _ _ Col_A_B_E) as (Col_B_A_E & Col_B_E_A & Col_E_A_B & Col_A_E_B & Col_E_B_A).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_E_B_G Col_E_B_A Col_E_B_B neq_A_B) as nCol_A_B_G.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_G) as (_ & _ & _ & _ & nCol_G_B_A).

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_G_F_E_B Col_E_B_A neq_A_B) as Par_G_F_A_B.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_G_F_A_B) as Par_A_B_G_F.

	pose proof (lemma_extension G B G B neq_G_B neq_G_B) as (q & BetS_G_B_q & Cong_B_q_G_B).
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_B_q) as BetS_q_B_G.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_G_B_q) as (neq_B_q & _ & neq_G_q).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_q_B_G) as (_ & neq_q_B & neq_q_G).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_G_B_q) as Col_G_B_q.
	pose proof (by_prop_Col_order _ _ _ Col_G_B_q) as (Col_B_G_q & Col_B_q_G & Col_q_G_B & Col_G_q_B & Col_q_B_G).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_G_B_A Col_G_B_q Col_G_B_G neq_q_G) as nCol_q_G_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_q_G_A) as (nCol_G_q_A & _ & _ & _ & _).

	pose proof (proposition_31 _ _ _ _ BetS_G_B_q nCol_G_q_A) as (
		H & h & T &
		BetS_H_A_h &
		CongA_h_A_B_A_B_G & CongA_h_A_B_G_B_A & CongA_B_A_h_G_B_A &
		CongA_H_A_B_A_B_q & CongA_H_A_B_q_B_A & CongA_B_A_H_q_B_A &
		Par_H_h_G_q &
		Cong_H_A_B_q & Cong_A_h_G_B & Cong_A_T_T_B & Cong_H_T_T_q & Cong_G_T_T_h &
		BetS_H_T_q & BetS_G_T_h & BetS_A_T_B
	).

	assert (eq H H) as eq_H_H by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C A H H eq_H_H) as Col_A_H_H.
	pose proof (by_def_Col_from_eq_B_C H A A eq_A_A) as Col_H_A_A.
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_A_h) as BetS_h_A_H.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_H_A_h) as (neq_A_h & neq_H_A & neq_H_h).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_h_A_H) as (neq_A_H & neq_h_A & neq_h_H).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_H_A_h) as Col_H_A_h.
	pose proof (by_prop_Col_order _ _ _ Col_H_A_h) as (Col_A_H_h & Col_A_h_H & Col_h_H_A & Col_H_h_A & Col_h_A_H).

	pose proof (by_prop_Par_flip _ _ _ _ Par_H_h_G_q) as (_ & Par_H_h_q_G & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_H_h_q_G Col_q_G_B neq_B_G) as Par_H_h_B_G.
	pose proof (by_prop_Par_flip _ _ _ _ Par_H_h_B_G) as (_ & Par_H_h_G_B & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_H_h_G_B) as Par_G_B_H_h.
	pose proof (by_prop_Par_flip _ _ _ _ Par_G_B_H_h) as (_ & Par_G_B_h_H & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_G_B_h_H Col_h_H_A neq_A_H) as Par_G_B_A_H.
	pose proof (by_prop_Par_flip _ _ _ _ Par_G_B_A_H) as (_ & Par_G_B_H_A & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_G_B_H_A) as Par_H_A_G_B.
	pose proof (by_prop_Par_flip _ _ _ _ Par_H_A_G_B) as (_ & Par_H_A_B_G & _).

	pose proof (by_prop_Par_NC _ _ _ _ Par_G_B_H_A) as (_ & _ & nCol_B_H_A & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_B_H_A) as (_ & _ & nCol_A_B_H & _ & _).

	pose proof (by_def_Col_from_BetS_A_B_C A T B BetS_A_T_B) as Col_A_T_B.
	pose proof (by_prop_Col_order _ _ _ Col_A_T_B) as (_ & _ & _ & Col_A_B_T & _).

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_H_A_B_q Cong_B_q_G_B) as Cong_H_A_G_B.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_H_A_G_B Cong_G_B_F_E) as Cong_H_A_F_E.

	pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_A_B_T Col_A_B_B BetS_H_T_q BetS_G_B_q nCol_A_B_H nCol_A_B_G) as SameSide_H_G_A_B.
	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_H_G_A_B Col_A_B_E neq_A_E) as SameSide_H_G_A_E.

	assert (TarskiPar_B_E_G_F_2 := TarskiPar_B_E_G_F).
	destruct TarskiPar_B_E_G_F_2 as (_ & neq_G_F & n_Meet_B_E_G_F & SameSide_G_F_B_E).

	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_G_F_B_E) as SameSide_G_F_E_B.
	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_G_F_E_B Col_E_B_A neq_E_A) as SameSide_G_F_E_A.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_G_F_E_A) as SameSide_G_F_A_E.
	pose proof (lemma_samesidetransitive _ _ _ _ _ SameSide_H_G_A_E SameSide_G_F_A_E) as SameSide_H_F_A_E.

	pose proof (proposition_33B _ _ _ _ Par_H_A_G_B Cong_H_A_G_B SameSide_H_G_A_B) as (Par_H_G_A_B & Cong_H_G_A_B).

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_H_G_A_B) as Par_A_B_H_G.
	pose proof (by_prop_Par_flip _ _ _ _ Par_A_B_H_G) as (_ & Par_A_B_G_H & _).

	pose proof (lemma_Playfair _ _ _ _ _ Par_A_B_G_H Par_A_B_G_F) as Col_G_H_F.
	pose proof (by_prop_Col_order _ _ _ Col_G_H_F) as (_ & Col_H_F_G & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_G_H_F) as (Col_H_G_F & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_H_F_G) as (_ & Col_F_G_H & _ & _ & _).

	pose proof (by_def_Parallelogram _ _ _ _ Par_H_A_B_G Par_H_G_A_B) as Parallelogram_H_A_B_G.
	pose proof (by_prop_Parallelogram_flip _ _ _ _ Parallelogram_H_A_B_G) as Parallelogram_A_H_G_B.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_H_A_B_G) as Parallelogram_A_B_G_H.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_A_B_G_H) as Parallelogram_B_G_H_A.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_B_G_H_A) as Parallelogram_G_H_A_B.

	pose proof (proposition_30 _ _ _ _ _ _ _ _ _ Par_H_A_G_B Par_F_E_G_B BetS_A_B_E Col_H_A_A Col_G_B_B Col_F_E_E neq_H_A neq_G_B neq_F_E) as Par_H_A_F_E.

	pose proof (proposition_33B _ _ _ _ Par_H_A_F_E Cong_H_A_F_E SameSide_H_F_A_E) as (Par_H_F_A_E & _).
	pose proof (by_prop_Par_flip _ _ _ _ Par_H_A_F_E) as (_ & Par_H_A_E_F & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_H_A_F_E) as (_ & nCol_H_F_E & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_H_F_E) as (_ & _ & _ & _ & nCol_E_F_H).
	pose proof (by_prop_nCol_order _ _ _ nCol_E_F_H) as (_ & _ & nCol_H_E_F & _ & _).

	pose proof (by_def_Parallelogram _ _ _ _ Par_H_A_E_F Par_H_F_A_E) as Parallelogram_H_A_E_F.
	pose proof (lemma_diagonalsbisect _ _ _ _ Parallelogram_H_A_E_F) as (t & Midpoint_H_t_E & Midpoint_A_t_F).

	destruct Midpoint_H_t_E as (BetS_H_t_E & Cong_H_t_t_E).
	destruct Midpoint_A_t_F as (BetS_A_t_F & Cong_A_t_t_F).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_H_t_t_E) as (_ & _ & Cong_H_t_E_t).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_A_t_t_F) as (_ & _ & Cong_A_t_F_t).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_A_t_F_t) as (Cong_t_A_t_F & _ & _).

	pose proof (postulate_Euclid5 _ _ _ _ _ _ BetS_A_t_F BetS_H_t_E BetS_A_B_E Cong_H_t_E_t Cong_t_A_t_F nCol_H_E_F) as (K & BetS_H_B_K & BetS_F_E_K).

	assert (eq K K) as eq_K_K by (reflexivity).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_B_K) as BetS_K_B_H.
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_E_K) as BetS_K_E_F.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_F_E_K) as (neq_E_K & _ & neq_F_K).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_K_E_F) as (neq_E_F & neq_K_E & neq_K_F).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_F_E_K) as Col_F_E_K.
	pose proof (by_prop_Col_order _ _ _ Col_F_E_K) as (Col_E_F_K & Col_E_K_F & Col_K_F_E & Col_F_K_E & Col_K_E_F).

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_H_A_E_F Col_E_F_K neq_K_F) as Par_H_A_K_F.
	pose proof (by_prop_Par_flip _ _ _ _ Par_H_A_K_F) as (_ & Par_H_A_F_K & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_H_A_F_K) as Par_F_K_H_A.
	pose proof (by_prop_Par_flip _ _ _ _ Par_F_K_H_A) as (_ & Par_F_K_A_H & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_G_B_E_F Col_E_F_K neq_K_F) as Par_G_B_K_F.

	pose proof (lemma_triangletoparallelogram _ _ _ _ _ Par_F_K_A_H Col_A_H_H) as (L & Parallelogram_H_L_K_F & Col_A_H_L).

	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_H_L_K_F) as Parallelogram_L_K_F_H.
	pose proof (by_prop_Parallelogram_flip _ _ _ _ Parallelogram_L_K_F_H) as Parallelogram_K_L_H_F.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_K_L_H_F) as Parallelogram_L_H_F_K.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_L_H_F_K) as Parallelogram_H_F_K_L.

	pose proof (by_prop_Col_order _ _ _ Col_A_H_L) as (_ & _ & Col_L_A_H & _ & _).
	
	assert (Parallelogram_H_L_K_F_2 := Parallelogram_H_L_K_F).
	destruct Parallelogram_H_L_K_F_2 as (Par_H_L_K_F & Par_H_F_L_K).

	pose proof (by_prop_Par_NC _ _ _ _ Par_H_L_K_F) as (_ & _ & nCol_L_K_F & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_H_L_K_F) as (nCol_H_L_K & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_H_L_K) as (_ & _ & _ & neq_L_H & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_L_K_F) as (neq_L_K & _ & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_L_K) as neq_K_L.

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_H_F_L_K) as Par_L_K_H_F.
	pose proof (by_prop_Par_flip _ _ _ _ Par_L_K_H_F) as (Par_K_L_H_F & _ & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_K_L_H_F Col_H_F_G neq_G_F) as Par_K_L_G_F.
	pose proof (by_prop_Par_flip _ _ _ _ Par_K_L_G_F) as (_ & Par_K_L_F_G & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_K_L_F_G) as Par_F_G_K_L.

	assert (Par_H_F_L_K_2 := Par_H_F_L_K).
	destruct Par_H_F_L_K_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_H_F_L_K & _ & _).

	pose proof (by_prop_Par_collinear2 _ _ _ _ _ _ Par_G_B_F_E Col_F_E_E Col_F_E_K neq_E_K) as Par_G_B_E_K.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_G_B_E_K) as Par_E_K_G_B.
	pose proof (lemma_triangletoparallelogram _ _ _ _ _ Par_E_K_G_B Col_G_B_B) as (M & Parallelogram_B_M_K_E & Col_G_B_M).

	pose proof (by_def_Col_from_eq_B_C M K K eq_K_K) as Col_M_K_K.
	
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_B_M_K_E) as Parallelogram_M_K_E_B.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_M_K_E_B) as Parallelogram_K_E_B_M.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_K_E_B_M) as Parallelogram_E_B_M_K.
	pose proof (by_prop_Parallelogram_flip _ _ _ _ Parallelogram_B_M_K_E) as Parallelogram_M_B_E_K.

	pose proof (by_prop_Col_order _ _ _ Col_G_B_M) as (_ & _ & _ & Col_G_M_B & _).


	assert (Parallelogram_B_M_K_E_2 := Parallelogram_B_M_K_E).
	destruct Parallelogram_B_M_K_E_2 as (Par_B_M_K_E & Par_B_E_M_K).

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_B_E_M_K) as Par_M_K_B_E.
	pose proof (by_prop_Par_NC _ _ _ _ Par_B_E_M_K) as (_ & _ & nCol_E_M_K & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_B_E_M_K) as (_ & nCol_B_M_K & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_M_K) as (_ & _ & _ & neq_M_B & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_E_M_K) as (_ & neq_M_K & _ & _ & _ & _).

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_H_A_G_B Col_G_B_M neq_M_B) as Par_H_A_M_B.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_H_A_M_B) as Par_M_B_H_A.
	pose proof (by_prop_Par_flip _ _ _ _ Par_M_B_H_A) as (_ & Par_M_B_A_H & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_M_B_A_H Col_A_H_L neq_L_H) as Par_M_B_L_H.
	pose proof (by_prop_Par_flip _ _ _ _ Par_M_B_L_H) as (_ & Par_M_B_H_L & _).

	pose proof (proposition_30 _ _ _ _ _ _ _ _ _ Par_M_K_B_E Par_G_F_B_E BetS_K_E_F Col_M_K_K Col_B_E_E Col_G_F_F neq_M_K neq_B_E neq_G_F) as Par_M_K_G_F.
	pose proof (by_prop_Par_flip _ _ _ _ Par_M_K_G_F) as (_ & _ & Par_K_M_F_G).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_K_M_F_G) as Par_F_G_K_M.

	pose proof (lemma_Playfair _ _ _ _ _ Par_F_G_K_M Par_F_G_K_L) as Col_K_M_L.
	pose proof (by_prop_Col_order _ _ _ Col_K_M_L) as (Col_M_K_L & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_M_K_L) as (_ & _ & Col_L_M_K & _ & _).

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_B_E_M_K Col_M_K_L neq_L_K) as Par_B_E_L_K.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_B_E_L_K) as Par_L_K_B_E.
	pose proof (by_prop_Par_flip _ _ _ _ Par_L_K_B_E) as (_ & Par_L_K_E_B & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_L_K_E_B Col_E_B_A neq_A_B) as Par_L_K_A_B.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_L_K_A_B) as Par_A_B_L_K.
	pose proof (by_prop_Par_flip _ _ _ _ Par_A_B_L_K) as (_ & Par_A_B_K_L & _).

	pose proof (lemma_parallelbetween _ _ _ _ _ BetS_H_B_K Par_M_B_H_L Col_L_M_K) as BetS_L_M_K.
	pose proof (lemma_parallelbetween _ _ _ _ _ BetS_K_B_H Par_A_B_K_L Col_L_A_H) as BetS_L_A_H.
	pose proof (lemma_parallelbetween _ _ _ _ _ BetS_K_B_H Par_G_B_K_F Col_F_G_H) as BetS_F_G_H.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_L_A_H) as BetS_H_A_L.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_G_H) as BetS_H_G_F.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_H_G_F) as (_ & _ & neq_H_F).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_H_G_F) as (_ & neq_H_G & _).

	pose proof (
		proposition_43
		_ _ _ _ _ _ _ _ _
		Parallelogram_H_F_K_L
		BetS_H_A_L BetS_H_G_F BetS_L_M_K BetS_F_E_K BetS_H_B_K
		Parallelogram_G_H_A_B Parallelogram_E_B_M_K
	) as EqAreaQuad_B_E_F_G_L_M_B_A.
	pose proof (
		proposition_43B
		_ _ _ _ _ _ _ _ _
		Parallelogram_H_L_K_F
		BetS_H_G_F BetS_H_A_L BetS_F_E_K BetS_L_M_K
		Parallelogram_A_H_G_B Parallelogram_M_B_E_K
	) as Parallelogram_A_B_M_L.

	pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_H_G_F Col_L_M_K neq_H_F neq_L_K neq_H_G neq_M_K n_Meet_H_F_L_K BetS_H_B_K Col_G_M_B) as BetS_G_B_M.
	pose proof (proposition_15 _ _ _ _ _ BetS_G_B_M BetS_A_B_E nCol_G_B_A) as (_ & CongA_A_B_M_G_B_E).
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_A_B_M_G_B_E CongA_G_B_E_E_B_G) as CongA_A_B_M_E_B_G.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_A_B_M_E_B_G CongA_E_B_G_J_D_N) as CongA_A_B_M_J_D_N.

	exists M, L.
	split.
	exact Parallelogram_A_B_M_L.
	split.
	exact CongA_A_B_M_J_D_N.
	split.
	exact EqAreaQuad_B_E_F_G_L_M_B_A.
	exact BetS_G_B_M.
Qed.

End Euclid.
