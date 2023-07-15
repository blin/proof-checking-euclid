Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_Par.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_parallelflip :
	forall A B C D,
	Par A B C D ->
	Par B A C D /\ Par A B D C /\ Par B A D C.
Proof.
	intros A B C D.
	intros Par_AB_CD.

	destruct Par_AB_CD as (M & a & b & c & d & neq_A_B & neq_C_D & Col_A_B_a & Col_A_B_b & neq_a_b & Col_C_D_c & Col_C_D_d & neq_c_d & n_Meet_A_B_C_D & BetS_a_M_d & BetS_c_M_b).

	pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.
	pose proof (lemma_inequalitysymmetric _ _ neq_C_D) as neq_D_C.
	pose proof (lemma_inequalitysymmetric _ _ neq_c_d) as neq_d_c.
	pose proof (lemma_inequalitysymmetric _ _ neq_a_b) as neq_b_a.

	pose proof (lemma_collinearorder _ _ _ Col_A_B_a) as (Col_B_A_a & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_b) as (Col_B_A_b & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_D_c) as (Col_D_C_c & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_D_d) as (Col_D_C_d & _ & _ & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_a_M_d) as BetS_d_M_a.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_M_b) as BetS_b_M_c.

	assert (~ Meet A B D C) as n_Meet_A_B_D_C.
	{
		intro Meet_A_B_D_C.

		destruct Meet_A_B_D_C as (P & _ & _ & Col_A_B_P & Col_D_C_P).

		pose proof (lemma_collinearorder _ _ _ Col_D_C_P) as (Col_C_D_P & _ & _ & _ & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_P Col_C_D_P) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	assert (~ Meet B A C D) as n_Meet_B_A_C_D.
	{
		intro Meet_B_A_C_D.

		destruct Meet_B_A_C_D as (P & _ & _ & Col_B_A_P & Col_C_D_P).

		pose proof (lemma_collinearorder _ _ _ Col_B_A_P) as (Col_A_B_P & _ & _ & _ & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_P Col_C_D_P) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}


	assert (~ Meet B A D C) as n_Meet_B_A_D_C.
	{
		intro Meet_B_A_D_C.

		destruct Meet_B_A_D_C as (P & _ & _ & Col_B_A_P & Col_D_C_P).

		pose proof (lemma_collinearorder _ _ _ Col_B_A_P) as (Col_A_B_P & _ & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_D_C_P) as (Col_C_D_P & _ & _ & _ & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_P Col_C_D_P) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	pose proof (by_def_Par _ _ _ _ _ _ _ _ _ neq_B_A neq_C_D Col_B_A_a Col_B_A_b neq_a_b Col_C_D_c Col_C_D_d neq_c_d n_Meet_B_A_C_D BetS_a_M_d BetS_c_M_b) as Par_BA_CD.
	pose proof (by_def_Par _ _ _ _ _ _ _ _ _ neq_A_B neq_D_C Col_A_B_a Col_A_B_b neq_a_b Col_D_C_c Col_D_C_d neq_c_d n_Meet_A_B_D_C BetS_a_M_d BetS_c_M_b) as Par_AB_DC.
	pose proof (by_def_Par _ _ _ _ _ _ _ _ _ neq_B_A neq_D_C Col_B_A_a Col_B_A_b neq_a_b Col_D_C_c Col_D_C_d neq_c_d n_Meet_B_A_D_C BetS_a_M_d BetS_c_M_b) as Par_BA_DC.

	split.
	exact Par_BA_CD.
	split.
	exact Par_AB_DC.
	exact Par_BA_DC.
Qed.

End Euclid.
