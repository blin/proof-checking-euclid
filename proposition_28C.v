Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_collinearparallel.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_parallelsymmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_ss.
Require Import ProofCheckingEuclid.lemma_s_triangle.
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
	intros SumTwoRT_B_G_H_G_H_D.
	intros SS_B_D_G_H.

	assert (SS_B_D_G_H_2 := SS_B_D_G_H).
	destruct SS_B_D_G_H_2 as (_ & _ & _ & _ & _ & _ & _ & nCol_G_H_B & nCol_G_H_D).

	pose proof (lemma_NCdistinct _ _ _ nCol_G_H_D) as (_ & neq_H_D & _ & _ & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_H_D) as neq_D_H.
	pose proof (lemma_NCdistinct _ _ _ nCol_G_H_B) as (_ & _ & neq_G_B & _ & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_G_B) as neq_B_G.
	pose proof (lemma_extension B G G B neq_B_G neq_G_B) as (A & BetS_B_G_A & Cong_G_A_G_B).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_G_A) as BetS_A_G_B.
	pose proof (lemma_extension D H H D neq_D_H neq_H_D) as (C & BetS_D_H_C & Cong_H_C_H_D).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_H_C) as BetS_C_H_D.
	pose proof (proposition_28B _ _ _ _ _ _ BetS_A_G_B BetS_C_H_D SumTwoRT_B_G_H_G_H_D SS_B_D_G_H) as Par_A_B_C_D.
	pose proof (lemma_s_col_BetS_A_B_C D H C BetS_D_H_C) as Col_D_H_C.
	pose proof (lemma_collinearorder _ _ _ Col_D_H_C) as (_ & _ & Col_C_D_H & _ & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_A_B_C_D Col_C_D_H neq_H_D) as Par_A_B_H_D.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_A_B_H_D) as Par_H_D_A_B.
	pose proof (lemma_s_col_BetS_A_B_C B G A BetS_B_G_A) as Col_B_G_A.
	pose proof (lemma_collinearorder _ _ _ Col_B_G_A) as (_ & _ & Col_A_B_G & _ & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_H_D_A_B Col_A_B_G neq_G_B) as Par_H_D_G_B.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_H_D_G_B) as Par_G_B_H_D.

	exact Par_G_B_H_D.
Qed.

End Euclid.

