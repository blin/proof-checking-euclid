Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order .
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.proposition_28A.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_28D :
	forall B D E G H,
	BetS E G H ->
	CongA E G B G H D ->
	SameSide B D G H ->
	Par G B H D.
Proof.
	intros B D E G H.
	intros BetS_E_G_H.
	intros CongA_EGB_GHD.
	intros SameSide_B_D_GH.

	assert (SameSide_B_D_GH_2 := SameSide_B_D_GH).
	destruct SameSide_B_D_GH_2 as (_ & _ & _ & _ & _ & _ & _ & nCol_G_H_B & nCol_G_H_D).

	pose proof (by_prop_nCol_order _ _ _ nCol_G_H_B) as (nCol_H_G_B & nCol_H_B_G & nCol_B_G_H & nCol_G_B_H & nCol_B_H_G).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_G_H_B) as (neq_G_H & neq_H_B & neq_G_B & neq_H_G & neq_B_H & neq_B_G).

	pose proof (by_prop_nCol_order _ _ _ nCol_G_H_D) as (nCol_H_G_D & nCol_H_D_G & nCol_D_G_H & nCol_G_D_H & nCol_D_H_G).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_G_H_D) as (_ & neq_H_D & neq_G_D & _ & neq_D_H & neq_D_G).

	pose proof (lemma_extension _ _ _ _ neq_B_G neq_G_B) as (A & BetS_B_G_A & Cong_GA_GB).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_G_A) as BetS_A_G_B.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_G_A) as Col_B_G_A.
	pose proof (by_prop_Col_order _ _ _ Col_B_G_A) as (Col_G_B_A & Col_G_A_B & Col_A_B_G & Col_B_A_G & Col_A_G_B).

	pose proof (lemma_extension _ _ _ _ neq_D_H neq_H_D) as (C & BetS_D_H_C & Cong_HC_HD).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_H_C) as BetS_C_H_D.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_D_H_C) as Col_D_H_C.
	pose proof (by_prop_Col_order _ _ _ Col_D_H_C) as (Col_H_D_C & Col_H_C_D & Col_C_D_H & Col_D_C_H & Col_C_H_D).

	pose proof (proposition_28A _ _ _ _ _ _ _ BetS_A_G_B BetS_C_H_D BetS_E_G_H CongA_EGB_GHD SameSide_B_D_GH) as Par_AB_CD.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_AB_CD Col_C_D_H neq_H_D) as Par_AB_HD.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AB_HD) as Par_HD_AB.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_HD_AB Col_A_B_G neq_G_B) as Par_HD_GB.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_HD_GB) as Par_GB_HD.

	exact Par_GB_HD.
Qed.

End Euclid.
