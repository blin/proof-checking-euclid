Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_Lt_asymmetric.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_Lt_transitive.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_eq_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_diagonalsmeet.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.proposition_34.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_35helper :
	forall A B C D E F,
	Parallelogram A B C D ->
	Parallelogram E B C F ->
	BetS A D F ->
	Col A E F ->
	BetS A E F.
Proof.
	intros A B C D E F.
	intros Parallelogram_A_B_C_D.
	intros Parallelogram_E_B_C_F.
	intros BetS_A_D_F.
	intros Col_A_E_F.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq F F) as eq_F_F by (reflexivity).

	pose proof (cn_congruencereflexive A D) as Cong_AD_AD.
	pose proof (cn_congruencereflexive A F) as Cong_AF_AF.
	pose proof (cn_congruencereflexive D A) as Cong_DA_DA.
	pose proof (cn_congruencereflexive F A) as Cong_FA_FA.
	pose proof (cn_congruencereverse A D) as Cong_AD_DA.
	pose proof (cn_congruencereverse A F) as Cong_AF_FA.
	pose proof (cn_congruencereverse D A) as Cong_DA_AD.
	pose proof (cn_congruencereverse D E) as Cong_DE_ED.

	pose proof (by_def_Col_from_eq_A_B C C B eq_C_C) as Col_C_C_B.
	pose proof (by_def_Col_from_eq_A_C A D A eq_A_A) as Col_A_D_A.
	pose proof (by_def_Col_from_eq_A_C F C F eq_F_F) as Col_F_C_F.
	pose proof (by_def_Col_from_eq_B_C F A A eq_A_A) as Col_F_A_A.

	assert (Parallelogram_A_B_C_D_2 := Parallelogram_A_B_C_D).
	destruct Parallelogram_A_B_C_D_2 as (Par_AB_CD & Par_AD_BC).

	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (nCol_A_B_C & nCol_A_C_D & nCol_B_C_D & nCol_A_B_D).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AD_BC) as (nCol_A_D_B & _ & nCol_D_B_C & nCol_A_D_C).

	assert (Par_AD_BC_2 := Par_AD_BC).
	destruct Par_AD_BC_2 as (_ & _ & _ & _ & _ & neq_A_D & neq_B_C & _ & _ & _ & _ & _ & _ & n_Meet_A_D_B_C & _ & _).

	pose proof (by_prop_neq_symmetric _ _ neq_B_C) as neq_C_B.

	assert (Parallelogram_E_B_C_F_2 := Parallelogram_E_B_C_F).
	destruct Parallelogram_E_B_C_F_2 as (Par_EB_CF & Par_EF_BC).

	pose proof (by_prop_Par_flip _ _ _ _ Par_EB_CF) as (Par_BE_CF & Par_EB_FC & Par_BE_FC).
	pose proof (by_prop_Par_NC _ _ _ _ Par_EB_FC) as (nCol_E_B_F & nCol_E_F_C & nCol_B_F_C & nCol_E_B_C).
	pose proof (by_prop_nCol_order _ _ _ nCol_E_B_F) as (nCol_B_E_F & nCol_B_F_E & nCol_F_E_B & nCol_E_F_B & nCol_F_B_E).

	assert (Par_EB_CF_2 := Par_EB_CF).
	destruct Par_EB_CF_2 as (_ & _ & _ & _ & _ & neq_E_B & neq_C_F & _ & _ & _ & _ & _ & _ & n_Meet_E_B_C_F & _ & _).

	pose proof (by_prop_neq_symmetric _ _ neq_E_B) as neq_B_E.
	pose proof (by_prop_neq_symmetric _ _ neq_C_F) as neq_F_C.

	assert (Par_EB_FC_2 := Par_EB_FC).
	destruct Par_EB_FC_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_E_B_F_C & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_F) as BetS_F_D_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_D_F) as (neq_D_F & _ & neq_A_F).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_F_D_A) as (neq_D_A & neq_F_D & neq_F_A).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_D_F) as Col_A_D_F.
	pose proof (by_prop_Col_order _ _ _ Col_A_D_F) as (Col_D_A_F & Col_D_F_A & Col_F_A_D & Col_A_F_D & Col_F_D_A).

	pose proof (by_def_Lt _ _ _ _ _ BetS_A_D_F Cong_AD_AD) as Lt_AD_AF.
	pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_AD_AF Cong_AD_DA) as Lt_DA_AF.

	pose proof (by_prop_Col_order _ _ _ Col_A_E_F) as (Col_E_A_F & Col_E_F_A & Col_F_A_E & Col_A_F_E & Col_F_E_A).

	pose proof (proposition_34 _ _ _ _ Parallelogram_A_B_C_D) as (Cong_AD_BC & _ & _ & _ & _).
	pose proof (proposition_34 _ _ _ _ Parallelogram_E_B_C_F) as (Cong_EF_BC & _ & _ & _ & _).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AD_BC) as (Cong_DA_CB & Cong_DA_BC & Cong_AD_CB).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AD_BC) as Cong_BC_AD.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BC_AD) as (Cong_CB_DA & Cong_CB_AD & Cong_BC_DA).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_EF_BC) as (Cong_FE_CB & Cong_FE_BC & Cong_EF_CB).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_EF_BC) as Cong_BC_EF.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BC_EF) as (Cong_CB_FE & Cong_CB_EF & Cong_BC_FE).

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AD_BC Cong_BC_EF) as Cong_AD_EF.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AD_EF) as (Cong_DA_FE & Cong_DA_EF & Cong_AD_FE).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AD_EF) as Cong_EF_AD.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_EF_AD) as (Cong_FE_DA & Cong_FE_AD & Cong_EF_DA).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_F_A_E Col_F_A_D neq_F_A) as Col_A_E_D.
	pose proof (by_prop_Col_order _ _ _ Col_A_E_D) as (Col_E_A_D & Col_E_D_A & Col_D_A_E & Col_A_D_E & Col_D_E_A).

	pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_A_B_C_D) as (M & BetS_A_M_C & BetS_B_M_D).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_M_C) as BetS_C_M_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_M_C) as (neq_M_C & neq_A_M & neq_A_C).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_M_A) as (neq_M_A & neq_C_M & neq_C_A).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_M_C) as Col_A_M_C.
	pose proof (by_prop_Col_order _ _ _ Col_A_M_C) as (Col_M_A_C & Col_M_C_A & Col_C_A_M & Col_A_C_M & Col_C_M_A).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_D_B Col_A_D_A Col_A_D_F neq_A_F) as nCol_A_F_B.

	pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_B_M_D BetS_A_D_F nCol_A_F_B) as (Q & BetS_B_Q_F & BetS_A_M_Q).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_Q_F) as BetS_F_Q_B.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_M_Q) as Col_A_M_Q.
	pose proof (by_prop_Col_order _ _ _ Col_A_M_Q) as (Col_M_A_Q & Col_M_Q_A & Col_Q_A_M & Col_A_Q_M & Col_Q_M_A).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_M_A_Q Col_M_A_C neq_M_A) as Col_A_Q_C.
	pose proof (by_prop_Col_order _ _ _ Col_A_Q_C) as (_ & _ & _ & Col_A_C_Q & _).

	assert (~ Meet F A C B) as n_Meet_F_A_C_B.
	{
		intro Meet_F_A_C_B.

		destruct Meet_F_A_C_B as (p & _ & _ & Col_F_A_p & Col_C_B_p).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_F_A_D Col_F_A_p neq_F_A) as Col_A_D_p.
		pose proof (by_prop_Col_order _ _ _ Col_C_B_p) as (Col_B_C_p & _ & _ & _ & _).

		pose proof (by_def_Meet _ _ _ _ _ neq_A_D neq_B_C Col_A_D_p Col_B_C_p) as Meet_A_D_B_C.

		contradict Meet_A_D_B_C.
		exact n_Meet_A_D_B_C.
	}

	pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_F_A_A Col_C_C_B neq_F_A neq_C_B neq_F_A neq_C_B n_Meet_F_A_C_B BetS_F_Q_B Col_A_C_Q) as BetS_A_Q_C.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_Q_C) as BetS_C_Q_A.

	assert (~ eq A E) as n_eq_A_E.
	{
		intro eq_A_E.

		assert (Cong A F E F) as Cong_AF_EF by (rewrite <- eq_A_E; exact Cong_AF_AF).
		pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AF_EF Cong_EF_AD) as Cong_AF_AD.
		pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AF_AD) as Cong_AD_AF.

		pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_AD_AF Cong_AD_AF) as Lt_AF_AF.

		pose proof (by_prop_Lt_asymmetric _ _ _ _ Lt_AF_AF) as n_Lt_AF_AF.

		contradict Lt_AF_AF.
		exact n_Lt_AF_AF.
	}
	assert (neq_A_E := n_eq_A_E).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_D_C Col_A_D_A Col_A_D_E neq_A_E) as nCol_A_E_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_E_C) as (_ & _ & nCol_C_A_E & _ & _).

	assert (~ BetS A F E) as n_BetS_A_F_E.
	{
		intro BetS_A_F_E.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_F_E) as BetS_E_F_A.

		pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_C_Q_A BetS_E_F_A nCol_C_A_E) as (r & BetS_C_r_F & BetS_E_r_Q).

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_r_F) as Col_C_r_F.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_C_r_F) as (neq_r_F & _ & _).

		pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_E_r_Q BetS_F_Q_B nCol_F_B_E) as (H & BetS_E_H_B & BetS_F_r_H).

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_H_B) as Col_E_H_B.
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_F_r_H) as Col_F_r_H.

		pose proof (by_prop_Col_order _ _ _ Col_E_H_B) as (_ & _ & _ & Col_E_B_H & _).
		pose proof (by_prop_Col_order _ _ _ Col_C_r_F) as (_ & Col_r_F_C & _ & _ & _).
		pose proof (by_prop_Col_order _ _ _ Col_F_r_H) as (Col_r_F_H & _ & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_r_F_C Col_r_F_H neq_r_F) as Col_F_C_H.

		pose proof (by_def_Meet _ _ _ _ _ neq_E_B neq_F_C Col_E_B_H Col_F_C_H) as Meet_E_B_F_C.

		contradict Meet_E_B_F_C.
		exact n_Meet_E_B_F_C.
	}

	(* assert by cases *)
	assert (BetS A E F) as BetS_A_E_F.
	destruct Col_A_F_E as [ eq_A_F | [ eq_A_E | [ eq_F_E | [ BetS_F_A_E | [ BetS_A_F_E |  BetS_A_E_F ] ] ] ] ].
	{
		(* case eq_A_F *)
		assert (BetS A D A) as BetS_A_D_A by (setoid_rewrite eq_A_F at 2; exact BetS_A_D_F).
		pose proof (axiom_betweennessidentity A D) as n_BetS_A_D_A.

		contradict BetS_A_D_A.
		exact n_BetS_A_D_A.
	}
	{
		(* case eq_A_E *)
		contradict eq_A_E.
		exact neq_A_E.
	}
	{
		(* case eq_F_E *)
		pose proof (by_prop_eq_symmetric _ _ eq_F_E) as eq_E_F.
		pose proof (by_def_Col_from_eq_B_C B E F eq_E_F) as Col_B_E_F.
		pose proof (by_prop_Col_order _ _ _ Col_B_E_F) as (Col_E_B_F & _ & _ & _ & _).

		pose proof (by_def_Meet _ _ _ _ _ neq_E_B neq_F_C Col_E_B_F Col_F_C_F) as Meet_E_B_F_C.

		contradict Meet_E_B_F_C.
		exact n_Meet_E_B_F_C.
	}
	{
		(* case BetS_F_A_E *)
		pose proof (by_def_Lt _ _ _ _ _ BetS_F_A_E Cong_FA_FA) as Lt_FA_FE.

		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_F_D_A BetS_F_A_E) as BetS_D_A_E.
		pose proof (by_def_Lt _ _ _ _ _ BetS_D_A_E Cong_DA_DA) as Lt_DA_DE.

		pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_DA_DE Cong_DA_AD) as Lt_AD_DE.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_AD_DE Cong_DE_ED) as Lt_AD_ED.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_DA_AF Cong_AF_FA) as Lt_DA_FA.
		pose proof (by_prop_Lt_transitive _ _ _ _ _ _ Lt_DA_FA Lt_FA_FE) as Lt_DA_FE.
		pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_DA_FE Cong_DA_FE) as Lt_FE_FE.
		pose proof (by_prop_Lt_asymmetric _ _ _ _ Lt_FE_FE) as n_Lt_FE_FE.

		contradict Lt_FE_FE.
		exact n_Lt_FE_FE.
	}
	{
		(* case BetS_A_F_E *)
		contradict BetS_A_F_E.
		exact n_BetS_A_F_E.
	}
	{
		(* case BetS_A_E_F *)
		exact BetS_A_E_F.
	}

	exact BetS_A_E_F.
Qed.

End Euclid.
