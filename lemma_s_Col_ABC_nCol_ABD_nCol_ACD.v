Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_Col_ABC_nCol_ABD_nCol_ACD :
	forall A B C D,
	Col A B C ->
	nCol A B D ->
	neq A C ->
	nCol A C D.
Proof.
	intros A B C D.
	intros Col_A_B_C.
	intros nCol_A_B_D.
	intros neq_A_C.

	assert (~ Col A C D) as n_Col_A_C_D.
	{
		intros Col_A_C_D.

		pose proof (by_prop_neq_symmetric _ _ neq_A_C) as neq_C_A.
		pose proof (by_prop_Col_order _ _ _ Col_A_B_C) as (_ & _ & Col_C_A_B & _ & _).
		pose proof (by_prop_Col_order _ _ _ Col_A_C_D) as (Col_C_A_D & _ & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_A_B Col_C_A_D neq_C_A) as Col_A_B_D.

		contradict Col_A_B_D.
		pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_D) as n_Col_A_B_D.
		exact n_Col_A_B_D.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_A_C_D) as nCol_A_C_D.
	exact nCol_A_C_D.
Qed.

End Euclid.
