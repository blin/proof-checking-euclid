Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_ncol_ABD_col_ABC_col_ADE_ncol_ACD :
	forall A B D C E,
	nCol A B D ->
	Col A B C ->
	Col A D E ->
	neq A C ->
	nCol A C D.
Proof.
	intros A B D C E.
	intros nCol_A_B_D.
	intros Col_A_B_C.
	intros Col_A_D_E.
	intros neq_A_C.

	assert (~ Col A C D) as n_Col_A_C_D.
	{
		intros Col_A_C_D.

		pose proof (lemma_inequalitysymmetric _ _ neq_A_C) as neq_C_A.
		pose proof (lemma_collinearorder _ _ _ Col_A_B_C) as (_ & _ & Col_C_A_B & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_A_C_D) as (Col_C_A_D & _ & _ & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_A_B Col_C_A_D neq_C_A) as Col_A_B_D.

		contradict Col_A_B_D.
		pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_D) as n_Col_A_B_D.
		exact n_Col_A_B_D.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_C_D) as nCol_A_C_D.
	exact nCol_A_C_D.
Qed.

End Euclid.
