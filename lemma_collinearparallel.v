Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_s_meet.
Require Import ProofCheckingEuclid.lemma_s_par.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_collinearparallel :
	forall A B C c d,
	Par A B c d ->
	Col c d C ->
	neq C d ->
	Par A B C d.
Proof.
	intros A B C c d.
	intros Par_AB_cd.
	intros Col_c_d_C.
	intros neq_C_d.


	destruct Par_AB_cd as (R & a & b & p & q & neq_A_B & neq_c_d & Col_A_B_a & Col_A_B_b & neq_a_b & Col_c_d_p & Col_c_d_q & neq_p_q & n_Meet_A_B_c_d & BetS_a_R_q & BetS_p_R_b).

	pose proof (lemma_collinearorder _ _ _ Col_c_d_C) as (_ & _ & _ & _ & Col_C_d_c).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_c_d_C Col_c_d_p neq_c_d) as Col_d_C_p.
	pose proof (lemma_collinearorder _ _ _ Col_d_C_p) as (Col_C_d_p & _ & _ & _ & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_c_d_C Col_c_d_q neq_c_d) as Col_d_C_q.
	pose proof (lemma_collinearorder _ _ _ Col_d_C_q) as (Col_C_d_q & _ & _ & _ & _).

	assert (~ Meet A B C d) as n_Meet_A_B_C_d.
	{
		intro Meet_A_B_C_d.

		destruct Meet_A_B_C_d as (E & _ & _ & Col_A_B_E & Col_C_d_E).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_d_E Col_C_d_c neq_C_d) as Col_d_E_c.
		pose proof (lemma_collinearorder _ _ _ Col_d_E_c) as (_ & _ & Col_c_d_E & _ & _).
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_c_d Col_A_B_E Col_c_d_E) as Meet_A_B_c_d.

		contradict Meet_A_B_c_d.
		exact n_Meet_A_B_c_d.
	}

	pose proof (lemma_s_par _ _ _ _ _ _ _ _ _ neq_A_B neq_C_d Col_A_B_a Col_A_B_b neq_a_b Col_C_d_p Col_C_d_q neq_p_q n_Meet_A_B_C_d BetS_a_R_q BetS_p_R_b) as Par_AB_Cd.

	exact Par_AB_Cd.
Qed.

End Euclid.
