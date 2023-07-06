Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_planeseparation.
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
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_samenotopposite :
	forall A B C D,
	SS A B C D ->
	~ OS A C D B.
Proof.
	intros A B C D.
	intros SS_A_B_C_D.

	pose proof (lemma_samesidesymmetric _ _ _ _ SS_A_B_C_D) as (SS_B_A_C_D & _ & _).

	assert (~ OS A C D B) as n_OS_A_C_D_B.
	{
		intro OS_A_C_D_B.
		pose proof (lemma_planeseparation _ _ _ _ _ SS_B_A_C_D OS_A_C_D_B) as OS_B_C_D_B.

		destruct OS_B_C_D_B as (M & BetS_B_M_B & _).
		pose proof (axiom_betweennessidentity B M) as n_BetS_B_M_B.
		contradict BetS_B_M_B.
		exact n_BetS_B_M_B.
	}

	exact n_OS_A_C_D_B.
Qed.

End Euclid.
