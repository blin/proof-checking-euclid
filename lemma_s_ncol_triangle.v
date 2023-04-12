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
	intros Triangle_A_B_C.

	unfold Triangle in Triangle_A_B_C.
	exact Triangle_A_B_C.
Qed.

End Euclid.
