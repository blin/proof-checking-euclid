Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_crisscross.
Require Import ProofCheckingEuclid.lemma_parallelNC.
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
Require Import ProofCheckingEuclid.lemma_samenotopposite.
Require Import ProofCheckingEuclid.proposition_33.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_33B :
	forall A B C D,
	Par A B C D ->
	Cong A B C D ->
	SS A C B D ->
	Par A C B D /\ Cong A C B D.
Proof.
	intros A B C D.
	intros Par_A_B_C_D.
	intros Cong_A_B_C_D.
	intros SS_A_C_B_D.


	assert (~ CR A C B D) as n_CR_A_C_B_D.
	{
		intro CR_A_C_B_D.

		destruct CR_A_C_B_D as (M & BetS_A_M_C & BetS_B_M_D).
		pose proof (lemma_s_col_BetS_A_B_C B M D BetS_B_M_D) as Col_B_M_D.
		pose proof (lemma_collinearorder _ _ _ Col_B_M_D) as (_ & _ & _ & Col_B_D_M & _).
		pose proof (lemma_parallelNC _ _ _ _ Par_A_B_C_D) as (_ & _ & _ & nCol_A_B_D).
		pose proof (lemma_NCorder _ _ _ nCol_A_B_D) as (_ & nCol_B_D_A & _ & _ & _).
		pose proof (lemma_s_os _ _ _ _ _ BetS_A_M_C Col_B_D_M nCol_B_D_A) as OS_A_B_D_C.
		pose proof (lemma_samenotopposite _ _ _ _ SS_A_C_B_D) as n_OS_A_B_D_C.
		contradict OS_A_B_D_C.
		exact n_OS_A_B_D_C.
	}

	pose proof (lemma_crisscross _ _ _ _ Par_A_B_C_D n_CR_A_C_B_D) as CR_A_D_C_B.

	destruct CR_A_D_C_B as (m & BetS_A_m_D & BetS_C_m_B).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_m_B) as BetS_B_m_C.
	pose proof (proposition_33 _ _ _ _ _ Par_A_B_C_D Cong_A_B_C_D BetS_A_m_D BetS_B_m_C) as (Par_A_C_B_D & Cong_A_C_B_D).

	split.
	exact Par_A_C_B_D.
	exact Cong_A_C_B_D.
Qed.

End Euclid.
