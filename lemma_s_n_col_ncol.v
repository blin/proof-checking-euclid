Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_s_n_ncol_col.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_n_col_ncol :
	forall A B C,
	~ Col A B C ->
	nCol A B C.
Proof.
	intros A B C.
	intros n_Col_A_B_C.
	assert (~ ~ nCol A B C) as nn_nCol_A_B_C.
	{
		intros n_nCol_A_B_C.
		pose proof (lemma_s_n_ncol_col _ _ _ n_nCol_A_B_C) as Col_A_B_C.
		contradiction n_Col_A_B_C.
	}
	apply Classical_Prop.NNPP in nn_nCol_A_B_C.
	exact nn_nCol_A_B_C.
Qed.

End Euclid.

