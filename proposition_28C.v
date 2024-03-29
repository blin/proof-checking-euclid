Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.proposition_28B.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_28C :
	forall B D G H,
	SumTwoRT B G H G H D ->
	SameSide B D G H ->
	Par G B H D.
Proof.
	intros B D G H.
	intros SumTwoRT_BGH_GHD.
	intros SameSide_B_D_GH.

	assert (SameSide_B_D_GH_2 := SameSide_B_D_GH).
	destruct SameSide_B_D_GH_2 as (_ & _ & _ & _ & _ & _ & _ & nCol_G_H_B & nCol_G_H_D).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_G_H_B) as (_ & _ & neq_G_B & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_G_B) as neq_B_G.

	pose proof (by_prop_nCol_distinct _ _ _ nCol_G_H_D) as (_ & neq_H_D & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_H_D) as neq_D_H.

	pose proof (postulate_Euclid2 _ _ neq_B_G) as (A & BetS_B_G_A).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_G_A) as BetS_A_G_B.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_G_A) as Col_B_G_A.
	pose proof (by_prop_Col_order _ _ _ Col_B_G_A) as (_ & _ & Col_A_B_G & _ & _).

	pose proof (postulate_Euclid2 _ _ neq_D_H) as (C & BetS_D_H_C).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_H_C) as BetS_C_H_D.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_D_H_C) as Col_D_H_C.
	pose proof (by_prop_Col_order _ _ _ Col_D_H_C) as (_ & _ & Col_C_D_H & _ & _).

	pose proof (proposition_28B _ _ _ _ _ _ BetS_A_G_B BetS_C_H_D SumTwoRT_BGH_GHD SameSide_B_D_GH) as Par_AB_CD.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_AB_CD Col_C_D_H neq_H_D) as Par_AB_HD.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AB_HD) as Par_HD_AB.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_HD_AB Col_A_B_G neq_G_B) as Par_HD_GB.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_HD_GB) as Par_GB_HD.

	exact Par_GB_HD.
Qed.

End Euclid.
