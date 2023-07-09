Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_collinearparallel.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_parallelsymmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.proposition_28B.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_28C :
	forall B D G H,
	SumTwoRT B G H G H D ->
	SS B D G H ->
	Par G B H D.
Proof.
	intros B D G H.
	intros SumTwoRT_BGH_GHD.
	intros SS_B_D_GH.

	assert (SS_B_D_GH_2 := SS_B_D_GH).
	destruct SS_B_D_GH_2 as (_ & _ & _ & _ & _ & _ & _ & nCol_G_H_B & nCol_G_H_D).

	pose proof (lemma_NCdistinct _ _ _ nCol_G_H_B) as (_ & _ & neq_G_B & _ & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_G_B) as neq_B_G.

	pose proof (lemma_NCdistinct _ _ _ nCol_G_H_D) as (_ & neq_H_D & _ & _ & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_H_D) as neq_D_H.

	pose proof (postulate_Euclid2 _ _ neq_B_G) as (A & BetS_B_G_A).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_G_A) as BetS_A_G_B.
	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_B_G_A) as Col_B_G_A.
	pose proof (lemma_collinearorder _ _ _ Col_B_G_A) as (_ & _ & Col_A_B_G & _ & _).

	pose proof (postulate_Euclid2 _ _ neq_D_H) as (C & BetS_D_H_C).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_H_C) as BetS_C_H_D.
	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_D_H_C) as Col_D_H_C.
	pose proof (lemma_collinearorder _ _ _ Col_D_H_C) as (_ & _ & Col_C_D_H & _ & _).

	pose proof (proposition_28B _ _ _ _ _ _ BetS_A_G_B BetS_C_H_D SumTwoRT_BGH_GHD SS_B_D_GH) as Par_AB_CD.
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_AB_CD Col_C_D_H neq_H_D) as Par_AB_HD.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_AB_HD) as Par_HD_AB.
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_HD_AB Col_A_B_G neq_G_B) as Par_HD_GB.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_HD_GB) as Par_GB_HD.

	exact Par_GB_HD.
Qed.

End Euclid.
