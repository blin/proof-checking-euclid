Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_Par.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct .
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.proposition_29.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_29C :
	forall B D E G H,
	Par G B H D ->
	SameSide B D G H ->
	BetS E G H ->
	CongA E G B G H D /\ SumTwoRT B G H G H D.
Proof.
	intros B D E G H.
	intros Par_GB_HD.
	intros SameSide_B_D_GH.
	intros BetS_E_G_H.

	assert (eq G G) as eq_G_G by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C G H G eq_G_G) as Col_G_H_G.

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_GB_HD) as Par_HD_GB.
	pose proof (by_prop_Par_NC _ _ _ _ Par_GB_HD) as (nCol_G_B_H & _ & _ & _).

	pose proof (by_prop_nCol_order _ _ _ nCol_G_B_H) as (nCol_B_G_H & nCol_B_H_G & nCol_H_G_B & nCol_G_H_B & nCol_H_B_G).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_G_B_H) as (neq_G_B & neq_B_H & neq_G_H & neq_B_G & neq_H_B & neq_H_G).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_B_D_GH) as (SameSide_D_B_GH & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_G_H) as BetS_H_G_E.

	pose proof (lemma_extension _ _ _ _ neq_B_G neq_B_G) as (A & BetS_B_G_A & Cong_GA_BG).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_G_A) as BetS_A_G_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_G_A) as (neq_G_A & _ & neq_B_A).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_G_B) as (_ & neq_A_G & neq_A_B).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_G_A) as Col_B_G_A.
	pose proof (by_prop_Col_order _ _ _ Col_B_G_A) as (Col_G_B_A & Col_G_A_B & Col_A_B_G & Col_B_A_G & Col_A_G_B).

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_B_G_A Col_G_H_G nCol_G_H_B) as OppositeSide_B_GH_A.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_D_B_GH OppositeSide_B_GH_A) as OppositeSide_D_GH_A.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_D_GH_A) as OppositeSide_A_GH_D.

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_HD_GB Col_G_B_A neq_A_B) as Par_HD_AB.
	pose proof (by_prop_Par_flip _ _ _ _ Par_HD_AB) as (_ & Par_HD_BA & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_HD_BA Col_B_A_G neq_G_A) as Par_HD_GA.
	pose proof (by_prop_Par_flip _ _ _ _ Par_HD_GA) as (_ & Par_HD_AG & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_HD_AG) as Par_AG_HD.

	destruct Par_AG_HD as (a & g & h & d & m & _ & neq_H_D & Col_A_G_a & Col_A_G_g & neq_a_g & Col_H_D_h & Col_H_D_d & neq_h_d & n_Meet_A_G_H_D & BetS_a_m_d & BetS_h_m_g).

	pose proof (by_prop_neq_symmetric _ _ neq_H_D) as neq_D_H.

	pose proof (lemma_extension _ _ _ _ neq_D_H neq_D_H) as (C & BetS_D_H_C & Cong_HC_DH).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_H_C) as BetS_C_H_D.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_D_H_C) as (neq_H_C & _ & neq_D_C).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_H_D) as (_ & neq_C_H & neq_C_D).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_D_H_C) as Col_D_H_C.
	pose proof (by_prop_Col_order _ _ _ Col_D_H_C) as (Col_H_D_C & Col_H_C_D & Col_C_D_H & Col_D_C_H & Col_C_H_D).

	pose proof (by_prop_Col_order _ _ _ Col_A_G_a) as (Col_G_A_a & _ & _ & _ & _).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_G_A_B Col_G_A_a neq_G_A) as Col_A_B_a.
	pose proof (by_prop_Col_order _ _ _ Col_A_G_g) as (Col_G_A_g & _ & _ & _ & _).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_G_A_B Col_G_A_g neq_G_A) as Col_A_B_g.
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_H_D_C Col_H_D_h neq_H_D) as Col_D_C_h.
	pose proof (by_prop_Col_order _ _ _ Col_D_C_h) as (Col_C_D_h & _ & _ & _ & _).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_H_D_d Col_H_D_C neq_H_D) as Col_D_d_C.
	pose proof (by_prop_Col_order _ _ _ Col_D_d_C) as (_ & _ & Col_C_D_d & _ & _).

	assert (~ Meet A B C D) as n_Meet_A_B_C_D.
	{
		intro Meet_A_B_C_D.

		destruct Meet_A_B_C_D as (M & _ & _ & Col_A_B_M & Col_C_D_M).

		pose proof (by_prop_Col_order _ _ _ Col_A_B_M) as (Col_B_A_M & _ & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_A_G Col_B_A_M neq_B_A) as Col_A_G_M.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_D_H Col_C_D_M neq_C_D) as Col_D_H_M.
		pose proof (by_prop_Col_order _ _ _ Col_D_H_M) as (Col_H_D_M & _ & _ & _ & _).

		pose proof (by_def_Meet _ _ _ _ _ neq_A_G neq_H_D Col_A_G_M Col_H_D_M) as Meet_A_G_H_D.

		contradict Meet_A_G_H_D.
		exact n_Meet_A_G_H_D.
	}

	pose proof (by_def_Par _ _ _ _ _ _ _ _ _ neq_A_B neq_C_D Col_A_B_a Col_A_B_g neq_a_g Col_C_D_h Col_C_D_d neq_h_d n_Meet_A_B_C_D BetS_a_m_d BetS_h_m_g) as Par_AB_CD.

	pose proof (proposition_29 _ _ _ _ _ _ _ Par_AB_CD BetS_A_G_B BetS_C_H_D BetS_E_G_H OppositeSide_A_GH_D) as (CongA_AGH_GHD & CongA_EGB_GHD & SumTwoRT_BGH_GHD).

	split.
	exact CongA_EGB_GHD.
	exact SumTwoRT_BGH_GHD.
Qed.

End Euclid.
