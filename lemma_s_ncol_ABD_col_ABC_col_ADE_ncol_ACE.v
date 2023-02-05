Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_permutations.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_ncol_ABD_col_ABC_col_ADE_ncol_ACE :
	forall A B D C E,
	nCol A B D ->
	Col A B C ->
	Col A D E ->
	neq A C ->
	neq A E ->
	nCol A C E.
Proof.
	intros A B D C E.
	intros nCol_A_B_D.
	intros Col_A_B_C.
	intros Col_A_D_E.
	intros neq_A_C.
	intros neq_A_E.


	assert (~ Col A C E) as n_Col_A_C_E.
	{
		intros Col_A_C_E.

		pose proof (lemma_inequalitysymmetric _ _ neq_A_C) as neq_C_A.
		pose proof (lemma_collinearorder _ _ _ Col_A_C_E) as (Col_C_A_E & _ & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_A_B_C) as (_ & _ & Col_C_A_B & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_A_E Col_C_A_B neq_C_A) as Col_A_E_B.

		pose proof (lemma_inequalitysymmetric _ _ neq_A_E) as neq_E_A.
		pose proof (lemma_collinearorder _ _ _ Col_A_D_E) as (_ & _ & Col_E_A_D & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_A_E_B) as (Col_E_A_B & _ & _ & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_A_B Col_E_A_D neq_E_A) as Col_A_B_D.

		contradict Col_A_B_D.
		pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_D) as n_Col_A_B_D.
		exact n_Col_A_B_D.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_C_E) as nCol_A_C_E.
	exact nCol_A_C_E.
Qed.

End Euclid.
