Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_nCol_helper :
	forall A B C P Q,
	nCol A B C ->
	Col A B P ->
	Col A B Q ->
	neq P Q ->
	nCol P Q C.
Proof.
	intros A B C P Q.
	intros nCol_A_B_C.
	intros Col_A_B_P.
	intros Col_A_B_Q.
	intros neq_P_Q.

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & _ & _ & neq_B_A & _ & _).
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_B_P Col_A_B_Q neq_A_B) as Col_B_P_Q.
	pose proof (by_prop_Col_order _ _ _ Col_A_B_P) as (Col_B_A_P & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_A_B_Q) as (Col_B_A_Q & _ & _ & _ & _).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_A_P Col_B_A_Q neq_B_A) as Col_A_P_Q.
	pose proof (by_prop_Col_order _ _ _ Col_A_P_Q) as (_ & Col_P_Q_A & _ & _ & _).

	pose proof (by_prop_Col_order _ _ _ Col_B_P_Q) as (_ & Col_P_Q_B & _ & _ & _).

	assert (~ Col P Q C) as n_Col_P_Q_C.
	{
		intros Col_P_Q_C.

		pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_P_Q Col_P_Q_A Col_P_Q_B Col_P_Q_C) as Col_A_B_C.

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_P_Q_C) as nCol_P_Q_C.

	exact nCol_P_Q_C.
Qed.

End Euclid.
