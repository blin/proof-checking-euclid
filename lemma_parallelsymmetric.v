Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_Par.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_parallelsymmetric :
	forall A B C D,
	Par A B C D ->
	Par C D A B.
Proof.
	intros A B C D.
	intros Par_AB_CD.


	destruct Par_AB_CD as (a & b & c & d & m & neq_A_B & neq_C_D & Col_A_B_a & Col_A_B_b & neq_a_b & Col_C_D_c & Col_C_D_d & neq_c_d & n_Meet_A_B_C_D & BetS_a_m_d & BetS_c_m_b).

	assert (~ Meet C D A B) as n_Meet_C_D_A_B.
	{
		intro Meet_C_D_A_B.

		destruct Meet_C_D_A_B as (P & _ & _ & Col_C_D_P & Col_A_B_P).
		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_P Col_C_D_P) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	pose proof (by_def_Par _ _ _ _ _ _ _ _ _ neq_C_D neq_A_B Col_C_D_c Col_C_D_d neq_c_d Col_A_B_a Col_A_B_b neq_a_b n_Meet_C_D_A_B BetS_c_m_b BetS_a_m_d) as Par_CD_AB.

	exact Par_CD_AB.
Qed.

End Euclid.

