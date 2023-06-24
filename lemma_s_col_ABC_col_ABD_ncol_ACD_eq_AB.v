Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_collinearorder.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB :
	forall A B C D,
	Col A B C ->
	Col A B D ->
	nCol A C D ->
	eq A B.
Proof.
	intros A B C D.
	intros Col_A_B_C.
	intros Col_A_B_D.
	intros nCol_A_C_D.

	pose proof (lemma_collinearorder _ _ _ Col_A_B_C) as (Col_B_A_C & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_D) as (Col_B_A_D & _ & _ & _ & _).

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_C_D) as n_Col_A_C_D.

	assert (~ neq A B) as n_neq_A_B.
	{
		intro neq_A_B.

		pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_C Col_B_A_D neq_B_A) as Col_A_C_D.

		contradict Col_A_C_D.
		exact n_Col_A_C_D.
	}
	assert (eq_A_B := n_neq_A_B).
	apply Classical_Prop.NNPP in eq_A_B.

	exact eq_A_B.
Qed.

End Euclid.
