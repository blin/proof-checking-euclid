Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_col_BetS_A_B_C :
	forall A B C,
	BetS A B C ->
	Col A B C.
Proof.
	intros A B C.
	intros BetS_A_B_C.

	unfold Col.
	repeat (exact BetS_A_B_C || (left; exact BetS_A_B_C) || right).
Qed.

End Euclid.
