Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_col_eq_A_B :
	forall A B C,
	eq A B ->
	Col A B C.
Proof.
	intros A B C.
	intros eq_A_B.

	unfold Col.
	repeat (exact eq_A_B || (left; exact eq_A_B) || right).
Qed.

End Euclid.
