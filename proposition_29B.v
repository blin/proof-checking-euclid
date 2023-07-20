Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_Par.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.proposition_29.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_29B :
	forall A D G H,
	Par A G H D ->
	OppositeSide A G H D ->
	CongA A G H G H D.
Proof.
	intros A D G H.
	intros Par_AG_HD.
	intros OppositeSide_A_GH_D.

	assert (eq G G) as eq_G_G by (reflexivity).
	assert (eq H H) as eq_H_H by (reflexivity).

	pose proof (by_def_Col_from_eq_A_C H D H eq_H_H) as Col_H_D_H.
	pose proof (by_def_Col_from_eq_B_C A G G eq_G_G) as Col_A_G_G.

	pose proof (by_prop_Par_NC _ _ _ _ Par_AG_HD) as (nCol_A_G_H & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_G_H) as (neq_A_G & neq_G_H & neq_A_H & neq_G_A & neq_H_G & neq_H_A).

	destruct Par_AG_HD as (a & g & h & d & m & _ & neq_H_D & Col_A_G_a & Col_A_G_g & neq_a_g & Col_H_D_h & Col_H_D_d & neq_h_d & n_Meet_A_G_H_D & BetS_a_m_d & BetS_h_m_g).

	pose proof (by_prop_neq_symmetric _ _ neq_H_D) as neq_D_H.

	pose proof (by_prop_Col_order _ _ _ Col_A_G_a) as (Col_G_A_a & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_A_G_g) as (Col_G_A_g & _ & _ & _ & _).

	pose proof (postulate_Euclid2 _ _ neq_A_G) as (B & BetS_A_G_B).
	pose proof (postulate_Euclid2 _ _ neq_D_H) as (C & BetS_D_H_C).
	pose proof (postulate_Euclid2 _ _ neq_H_G) as (E & BetS_H_G_E).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_G_B) as (_ & _ & neq_A_B).
	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_G_B) as Col_A_G_B.
	pose proof (by_prop_Col_order _ _ _ Col_A_G_B) as (Col_G_A_B & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_A_G_B) as (_ & _ & Col_B_A_G & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_H_C) as BetS_C_H_D.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_D_H_C) as (_ & _ & neq_D_C).
	pose proof (by_prop_neq_symmetric _ _ neq_D_C) as neq_C_D.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_D_H_C) as Col_D_H_C.
	pose proof (by_prop_Col_order _ _ _ Col_D_H_C) as (Col_H_D_C & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_D_H_C) as (_ & _ & Col_C_D_H & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_G_E) as BetS_E_G_H.

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_G_A_B Col_G_A_a neq_G_A) as Col_A_B_a.
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

	exact CongA_AGH_GHD.
Qed.

End Euclid.
