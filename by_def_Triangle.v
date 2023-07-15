Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_Triangle :
	forall A B C,
	nCol A B C ->
	Triangle A B C.
Proof.
	intros A B C.
	intros nCol_A_B_C.

	unfold Triangle.
	exact nCol_A_B_C.
Qed.

End Euclid.
