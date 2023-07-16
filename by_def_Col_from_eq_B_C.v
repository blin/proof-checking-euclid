Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_Col_from_eq_B_C :
	forall A B C,
	eq B C ->
	Col A B C.
Proof.
	intros A B C.
	intros eq_B_C.

	unfold Col.
	repeat (exact eq_B_C || (left; exact eq_B_C) || right).
Qed.

End Euclid.
