Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_col_eq_A_C :
	forall A B C,
	eq A C ->
	Col A B C.
Proof.
	intros A B C.
	intros eq_A_C.

	unfold Col.
	repeat (exact eq_A_C || (left; exact eq_A_C) || right).
Qed.

End Euclid.
