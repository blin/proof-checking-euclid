Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_ncol_triangle :
	forall A B C,
	Triangle A B C ->
	nCol A B C.
Proof.
	intros A B C.
	intros Triangle_ABC.

	unfold Triangle in Triangle_ABC.
	exact Triangle_ABC.
Qed.

End Euclid.
