Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_meet.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_par.
Require Import ProofCheckingEuclid.lemma_s_triangle.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_parallelflip :
	forall A B C D,
	Par A B C D ->
	Par B A C D /\ Par A B D C /\ Par B A D C.
Proof.
	intros A B C D.
	intros Par_A_B_C_D.


	destruct Par_A_B_C_D as (M & a & b & c & d & neq_A_B & neq_C_D & Col_A_B_a & Col_A_B_b & neq_a_b & Col_C_D_c & Col_C_D_d & neq_c_d & n_Meet_A_B_C_D & BetS_a_M_d & BetS_c_M_b).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_a) as (Col_B_A_a & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_b) as (Col_B_A_b & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_D_c) as (Col_D_C_c & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_D_d) as (Col_D_C_d & _ & _ & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.
	pose proof (lemma_inequalitysymmetric _ _ neq_C_D) as neq_D_C.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_a_M_d) as BetS_d_M_a.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_M_b) as BetS_b_M_c.
	pose proof (lemma_inequalitysymmetric _ _ neq_c_d) as neq_d_c.
	pose proof (lemma_inequalitysymmetric _ _ neq_a_b) as neq_b_a.

	assert (~ Meet A B D C) as n_Meet_A_B_D_C.
	{
		intro Meet_A_B_D_C.

		destruct Meet_A_B_D_C as (P & _ & _ & Col_A_B_P & Col_D_C_P).
		pose proof (lemma_collinearorder _ _ _ Col_D_C_P) as (Col_C_D_P & _ & _ & _ & _).
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_P Col_C_D_P) as Meet_A_B_C_D.
		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}


	assert (~ Meet B A C D) as n_Meet_B_A_C_D.
	{
		intro Meet_B_A_C_D.

		destruct Meet_B_A_C_D as (P & _ & _ & Col_B_A_P & Col_C_D_P).
		pose proof (lemma_collinearorder _ _ _ Col_B_A_P) as (Col_A_B_P & _ & _ & _ & _).
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_P Col_C_D_P) as Meet_A_B_C_D.
		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}


	assert (~ Meet B A D C) as n_Meet_B_A_D_C.
	{
		intro Meet_B_A_D_C.

		destruct Meet_B_A_D_C as (P & _ & _ & Col_B_A_P & Col_D_C_P).
		pose proof (lemma_collinearorder _ _ _ Col_B_A_P) as (Col_A_B_P & _ & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_D_C_P) as (Col_C_D_P & _ & _ & _ & _).
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_P Col_C_D_P) as Meet_A_B_C_D.
		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	pose proof (lemma_s_par _ _ _ _ _ _ _ _ _ neq_B_A neq_C_D Col_B_A_a Col_B_A_b neq_a_b Col_C_D_c Col_C_D_d neq_c_d n_Meet_B_A_C_D BetS_a_M_d BetS_c_M_b) as Par_B_A_C_D.
	pose proof (lemma_s_par _ _ _ _ _ _ _ _ _ neq_A_B neq_D_C Col_A_B_a Col_A_B_b neq_a_b Col_D_C_c Col_D_C_d neq_c_d n_Meet_A_B_D_C BetS_a_M_d BetS_c_M_b) as Par_A_B_D_C.
	pose proof (lemma_s_par _ _ _ _ _ _ _ _ _ neq_B_A neq_D_C Col_B_A_a Col_B_A_b neq_a_b Col_D_C_c Col_D_C_d neq_c_d n_Meet_B_A_D_C BetS_a_M_d BetS_c_M_b) as Par_B_A_D_C.

	split.
	exact Par_B_A_C_D.
	split.
	exact Par_A_B_D_C.
	exact Par_B_A_D_C.
Qed.

End Euclid.
