Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_meet.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_parallelNC :
	forall A B C D,
	Par A B C D ->
	nCol A B C /\ nCol A C D /\ nCol B C D /\ nCol A B D.
Proof.
	intros A B C D.
	intros Par_AB_CD.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq D D) as eq_D_D by (reflexivity).

	pose proof (lemma_s_col_eq_A_C A B A eq_A_A) as Col_A_B_A.
	pose proof (lemma_s_col_eq_A_C C D C eq_C_C) as Col_C_D_C.
	pose proof (lemma_s_col_eq_B_C A B B eq_B_B) as Col_A_B_B.
	pose proof (lemma_s_col_eq_B_C C D D eq_D_D) as Col_C_D_D.

	destruct Par_AB_CD as (a & b & c & d & M & neq_A_B & neq_C_D & Col_A_B_a & Col_A_B_b & neq_a_b & Col_C_D_c & Col_C_D_d & neq_c_d & n_Meet_A_B_C_D & BetS_a_M_d & BetS_c_M_b).

	assert (~ Col A C D) as n_Col_A_C_D.
	{
		intro Col_A_C_D.

		pose proof (lemma_collinearorder _ _ _ Col_A_C_D) as (_ & Col_C_D_A & _ & _ & _).
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_A Col_C_D_A) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_C_D) as nCol_A_C_D.


	assert (~ Col A B C) as n_Col_A_B_C.
	{
		intro Col_A_B_C.

		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_C Col_C_D_C) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_B_C) as nCol_A_B_C.


	assert (~ Col B C D) as n_Col_B_C_D.
	{
		intro Col_B_C_D.

		pose proof (lemma_collinearorder _ _ _ Col_B_C_D) as (_ & Col_C_D_B & _ & _ & _).
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_B Col_C_D_B) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_B_C_D) as nCol_B_C_D.


	assert (~ Col A B D) as n_Col_A_B_D.
	{
		intro Col_A_B_D.

		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_D Col_C_D_D) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_B_D) as nCol_A_B_D.

	split.
	exact nCol_A_B_C.
	split.
	exact nCol_A_C_D.
	split.
	exact nCol_B_C_D.
	exact nCol_A_B_D.


Qed.

End Euclid.
