Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_lt.
Require Import ProofCheckingEuclid.lemma_s_lta.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_ss.
Require Import ProofCheckingEuclid.lemma_s_triangle.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_samesidereflexive :
	forall A B P,
	nCol A B P ->
	SS P P A B.
Proof.
	intros A B P.
	intros nCol_A_B_P.

	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_P) as (neq_A_B & neq_B_P & neq_A_P & neq_B_A & neq_P_B & neq_P_A).

	assert (eq A A) as eq_A_A by (reflexivity).

	pose proof (lemma_extension P A A P neq_P_A neq_A_P) as (C & BetS_P_A_C & Cong_A_C_A_P).
	pose proof (lemma_s_col_eq_A_C A B A eq_A_A) as Col_A_B_A.
	pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_A_B_A Col_A_B_A BetS_P_A_C BetS_P_A_C nCol_A_B_P nCol_A_B_P) as SS_P_P_A_B.

	exact SS_P_P_A_B.
Qed.

End Euclid.

