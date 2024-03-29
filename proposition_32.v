Require Import ProofCheckingEuclid.by_def_AngleSum.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_OnRay.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_flip.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABD_BCD_ACD.
Require Import ProofCheckingEuclid.proposition_29.
Require Import ProofCheckingEuclid.proposition_31short.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_32 :
	forall A B C D,
	Triangle A B C ->
	BetS B C D ->
	AngleSum C A B A B C A C D.
Proof.
	intros A B C D.
	intros Triangle_ABC.
	intros BetS_B_C_D.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq D D) as eq_D_D by (reflexivity).

	pose proof (by_def_Col_from_eq_B_C A B B eq_B_B) as Col_A_B_B.
	pose proof (by_def_Col_from_eq_B_C A C C eq_C_C) as Col_A_C_C.
	pose proof (by_def_Col_from_eq_B_C A D D eq_D_D) as Col_A_D_D.

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_ABC) as nCol_A_B_C.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_C_A_B) as CongA_CAB_BAC.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_C_B_A) as CongA_CBA_ABC.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_C_D) as BetS_D_C_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_C_D) as (neq_C_D & _ & _).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_C_D) as Col_B_C_D.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_D) as OnRay_CD_D.

	pose proof (postulate_Euclid2 _ _ neq_B_A) as (F & BetS_B_A_F).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_F) as BetS_F_A_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_A_F) as (_ & _ & neq_B_F).
	pose proof (by_prop_neq_symmetric _ _ neq_B_F) as neq_F_B.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_A_F) as Col_B_A_F.
	pose proof (by_prop_Col_order _ _ _ Col_B_A_F) as (Col_A_B_F & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_B_A_F) as (_ & _ & Col_F_B_A & _ & _).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_B_C Col_A_B_F Col_A_B_B neq_F_B) as nCol_F_B_C.

	pose proof (proposition_31short _ _ _ _ BetS_F_A_B nCol_F_B_C) as (
		E &
		H &
		S &
		BetS_E_C_H &
		CongA_ECA_CAB &
		Par_EH_FB &
		BetS_E_S_B &
		BetS_C_S_A
	).

	assert (eq E E) as eq_E_E by (reflexivity).
	assert (eq H H) as eq_H_H by (reflexivity).

	pose proof (by_def_Col_from_eq_A_C B S B eq_B_B) as Col_B_S_B.
	pose proof (by_def_Col_from_eq_B_C A H H eq_H_H) as Col_A_H_H.
	pose proof (by_def_Col_from_eq_B_C B E E eq_E_E) as Col_B_E_E.
	pose proof (by_def_Col_from_eq_B_C C E E eq_E_E) as Col_C_E_E.
	pose proof (by_def_Col_from_eq_B_C S C C eq_C_C) as Col_S_C_C.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_C_H) as BetS_H_C_E.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_C_H) as (_ & _ & neq_E_H).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_H_C_E) as (neq_C_E & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_E_H) as neq_H_E.

	pose proof (by_def_Col_from_BetS_B_A_C _ _ _ BetS_E_C_H) as Col_C_E_H.

	pose proof (by_prop_CongA_flip _ _ _ _ _ _ CongA_ECA_CAB) as CongA_ACE_BAC.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ACE_BAC) as CongA_BAC_ACE.

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_EH_FB Col_F_B_A neq_A_B) as Par_EH_AB.
	pose proof (by_prop_Par_flip _ _ _ _ Par_EH_AB) as (_ & Par_EH_BA & _).

	destruct Par_EH_FB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_E_H_F_B & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_S_B) as BetS_B_S_E.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_S_E) as (_ & _ & neq_B_E).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_S_E) as (neq_S_E & _ & _).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_S_B) as Col_E_S_B.
	pose proof (by_prop_Col_order _ _ _ Col_E_S_B) as (Col_S_E_B & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_E_S_B) as (_ & _ & Col_B_E_S & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_E_S_B) as (_ & _ & _ & _ & Col_B_S_E).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_S_A) as BetS_A_S_C.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_S_A) as (_ & neq_C_S & _).
	pose proof (by_prop_neq_symmetric _ _ neq_C_S) as neq_S_C.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_S_A) as Col_C_S_A.
	pose proof (by_prop_Col_order _ _ _ Col_C_S_A) as (_ & _ & _ & Col_C_A_S & _).
	pose proof (by_prop_Col_order _ _ _ Col_C_A_S) as (Col_A_C_S & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_C_S_A) as (Col_S_C_A & _ & _ & _ & _).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_C_B Col_A_C_S Col_A_C_C neq_S_C) as nCol_S_C_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_S_C_B) as (_ & _ & nCol_B_S_C & _ & _).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_S_C Col_B_S_B Col_B_S_E neq_B_E) as nCol_B_E_C.
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_E_C Col_B_E_S Col_B_E_E neq_S_E) as nCol_S_E_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_S_E_C) as (_ & _ & _ & nCol_S_C_E & _).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_S_C_E Col_S_C_C Col_S_C_A neq_C_A) as nCol_C_A_E.
	pose proof (by_prop_nCol_order _ _ _ nCol_C_A_E) as (_ & _ & _ & nCol_C_E_A & _).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_C_E_A Col_C_E_H Col_C_E_E neq_H_E) as nCol_H_E_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_H_E_A) as (nCol_E_H_A & _ & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_H_E_A) as (_ & _ & nCol_A_H_E & _ & _).


	pose proof (postulate_Euclid2 _ _ neq_A_C) as (K & BetS_A_C_K).
	pose proof (postulate_Euclid2 _ _ neq_A_B) as (M & BetS_A_B_M).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_K) as BetS_K_C_A.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_M) as BetS_M_B_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_B_M) as (_ & _ & neq_A_M).
	pose proof (by_prop_neq_symmetric _ _ neq_A_M) as neq_M_A.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_B_M) as Col_A_B_M.
	pose proof (by_prop_Col_order _ _ _ Col_A_B_M) as (_ & _ & Col_M_A_B & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_A_B_M) as (Col_B_A_M & _ & _ & _ & _).

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_EH_BA Col_B_A_M neq_M_A) as Par_EH_MA.
	pose proof (by_prop_Par_flip _ _ _ _ Par_EH_MA) as (Par_HE_MA & _ & _).

	pose proof (postulate_Euclid2 _ _ neq_H_E) as (L & BetS_H_E_L).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_E_L) as BetS_L_E_H.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_L_E_H) as (_ & _ & neq_L_H).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_L_E_H) as Col_L_E_H.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_H_E_L) as Col_H_E_L.
	pose proof (by_prop_Col_order _ _ _ Col_H_E_L) as (_ & _ & Col_L_H_E & _ & _).

	assert (~ Meet A M L H) as n_Meet_A_M_L_H.
	{
		intro Meet_A_M_L_H.

		destruct Meet_A_M_L_H as (c & _ & _ & Col_A_M_c & Col_L_H_c).

		pose proof (by_prop_Col_order _ _ _ Col_A_M_c) as (Col_M_A_c & _ & _ & _ & _).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_L_H_c Col_L_H_E neq_L_H) as Col_H_c_E.
		pose proof (by_prop_Col_order _ _ _ Col_H_c_E) as (_ & _ & Col_E_H_c & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_M_A_B Col_M_A_c neq_M_A) as Col_A_B_c.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_B_c Col_A_B_F neq_A_B) as Col_B_c_F.
		pose proof (by_prop_Col_order _ _ _ Col_B_c_F) as (_ & _ & Col_F_B_c & _ & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_E_H neq_F_B Col_E_H_c Col_F_B_c) as Meet_E_H_F_B.

		contradict Meet_E_H_F_B.
		exact n_Meet_E_H_F_B.
	}

	pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_A_S_C BetS_E_C_H nCol_E_H_A) as (Q & BetS_A_Q_H & BetS_E_S_Q).

	pose proof (by_def_Col_from_eq_B_C Q E E eq_E_E) as Col_Q_E_E.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_Q_H) as (neq_Q_H & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_Q_H) as (_ & _ & neq_A_H).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_Q_H) as Col_A_Q_H.
	pose proof (by_prop_Col_order _ _ _ Col_A_Q_H) as (_ & _ & _ & Col_A_H_Q & _).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_H_E Col_A_H_Q Col_A_H_H neq_Q_H) as nCol_Q_H_E.
	pose proof (by_prop_nCol_order _ _ _ nCol_Q_H_E) as (_ & _ & _ & nCol_Q_E_H & _).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_S_Q) as Col_E_S_Q.
	pose proof (by_prop_Col_order _ _ _ Col_E_S_Q) as (Col_S_E_Q & _ & _ & _ & _).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_S_E_B Col_S_E_Q neq_S_E) as Col_E_B_Q.
	pose proof (by_prop_Col_order _ _ _ Col_E_B_Q) as (Col_B_E_Q & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_E_B_Q) as (_ & _ & Col_Q_E_B & _ & _).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_Q_E_H Col_Q_E_B Col_Q_E_E neq_B_E) as nCol_B_E_H.

	pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_A_B_M Col_L_E_H neq_A_M neq_L_H neq_A_B neq_E_H n_Meet_A_M_L_H BetS_A_Q_H Col_B_E_Q) as BetS_B_Q_E.

	pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_B_Q_E BetS_H_C_E nCol_B_E_H) as (T & BetS_B_T_C & BetS_H_T_Q).

	pose proof (by_def_Col_from_eq_A_C A T A eq_A_A) as Col_A_T_A.

	pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_B_T_C BetS_B_C_D) as BetS_T_C_D.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_T_C_D) as (_ & _ & neq_T_D).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_T_C_D) as BetS_D_C_T.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_T_C) as Col_B_T_C.
	pose proof (by_prop_Col_order _ _ _ Col_B_T_C) as (_ & _ & Col_C_B_T & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_C_B_T) as (Col_B_C_T & _ & _ & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_T_Q) as BetS_Q_T_H.
	pose proof (lemma_orderofpoints_ABD_BCD_ACD _ _ _ _ BetS_A_Q_H BetS_Q_T_H) as BetS_A_T_H.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_T_H) as BetS_H_T_A.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_T_H) as Col_A_T_H.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_C_A Col_B_C_T Col_B_C_D neq_T_D) as nCol_T_D_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_T_D_A) as (_ & _ & nCol_A_T_D & _ & _).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_T_D Col_A_T_A Col_A_T_H neq_A_H) as nCol_A_H_D.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_H_D) as (nCol_H_A_D & _ & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_H_A_D) as (_ & nCol_A_D_H & _ & _ & _).

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_A_T_H Col_C_B_T nCol_C_B_A) as OppositeSide_A_CB_H.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_A_CB_H) as OppositeSide_H_CB_A.

	pose proof (proposition_29 _ _ _ _ _ _ _ Par_HE_MA BetS_H_C_E BetS_M_B_A BetS_D_C_B OppositeSide_H_CB_A) as (_ & CongA_DCE_CBA & _).
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_DCE_CBA CongA_CBA_ABC) as CongA_DCE_ABC.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_DCE_ABC) as CongA_ABC_DCE.

	pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_D_C_T BetS_H_T_A nCol_H_A_D) as (R & BetS_D_R_A & BetS_H_C_R).

	assert (eq R R) as eq_R_R by (reflexivity).

	pose proof (by_def_Col_from_eq_A_C R H R eq_R_R) as Col_R_H_R.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_R_A) as BetS_A_R_D.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_D_R_A) as (_ & neq_D_R & _).
	pose proof (by_prop_neq_symmetric _ _ neq_D_R) as neq_R_D.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_D_R_A) as Col_D_R_A.
	pose proof (by_prop_Col_order _ _ _ Col_D_R_A) as (_ & _ & Col_A_D_R & _ & _).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_H_C_R) as (neq_C_R & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_C_R) as neq_R_C.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_H_C_R) as Col_H_C_R.
	pose proof (by_prop_Col_order _ _ _ Col_H_C_R) as (_ & _ & Col_R_H_C & _ & _).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_D_H Col_A_D_R Col_A_D_D neq_R_D) as nCol_R_D_H.
	pose proof (by_prop_nCol_order _ _ _ nCol_R_D_H) as (_ & _ & _ & nCol_R_H_D & _).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_R_H_D Col_R_H_R Col_R_H_C neq_R_C) as nCol_R_C_D.
	pose proof (by_prop_nCol_order _ _ _ nCol_R_C_D) as (_ & _ & _ & _ & nCol_D_C_R).
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_D_C_R) as CongA_DCR_RCD.

	pose proof (by_def_OnRay _ _ _ _ BetS_H_C_E BetS_H_C_R) as OnRay_CE_R.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_A) as OnRay_CA_A.

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_BAC_ACE OnRay_CA_A OnRay_CE_R) as CongA_BAC_ACR.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_CAB_BAC CongA_BAC_ACR) as CongA_CAB_ACR.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_ABC_DCE OnRay_CD_D OnRay_CE_R) as CongA_ABC_DCR.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_DCR CongA_DCR_RCD) as CongA_ABC_RCD.

	pose proof (by_def_AngleSum _ _ _ _ _ _ _ _ _ _ CongA_CAB_ACR CongA_ABC_RCD BetS_A_R_D) as AngleSum_CAB_ABC_ACD.

	exact AngleSum_CAB_ABC_ACD.
Qed.

End Euclid.
