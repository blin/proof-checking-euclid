Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_Col_from_n_nCol.
Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_nCol_from_n_Col :
	forall A B C,
	~ Col A B C ->
	nCol A B C.
Proof.
	intros A B C.
	intros n_Col_A_B_C.
	assert (~ ~ nCol A B C) as nn_nCol_A_B_C.
	{
		intros n_nCol_A_B_C.

		pose proof (by_def_Col_from_n_nCol _ _ _ n_nCol_A_B_C) as Col_A_B_C.

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	apply Classical_Prop.NNPP in nn_nCol_A_B_C.
	exact nn_nCol_A_B_C.
Qed.

End Euclid.

