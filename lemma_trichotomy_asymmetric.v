Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_partnotequalwhole.
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
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_triangle.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_trichotomy_asymmetric :
	forall A B C D,
	Lt A B C D ->
	~ Lt C D A B.
Proof.
	intros A B C D.
	intros Lt_A_B_C_D.

	destruct Lt_A_B_C_D as (E & BetS_C_E_D & Cong_C_E_A_B).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_C_E_A_B) as Cong_A_B_C_E.

	assert (~ Lt C D A B) as n_Lt_C_D_A_B.
	{
		intro Lt_C_D_A_B.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_C_D_A_B Cong_A_B_C_E) as Lt_C_D_C_E.
		destruct Lt_C_D_C_E as (F & BetS_C_F_E & Cong_C_F_C_D).
		pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_C_F_E BetS_C_E_D) as BetS_C_F_D.
		pose proof (lemma_partnotequalwhole _ _ _ BetS_C_F_D) as n_Cong_C_F_C_D.
		contradict Cong_C_F_C_D.
		exact n_Cong_C_F_C_D.
	}

	exact n_Lt_C_D_A_B.
Qed.

End Euclid.
