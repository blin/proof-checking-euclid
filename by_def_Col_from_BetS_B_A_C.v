Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_Col_from_BetS_B_A_C :
	forall A B C,
	BetS B A C ->
	Col A B C.
Proof.
	intros A B C.
	intros BetS_B_A_C.

	unfold Col.
	repeat (exact BetS_B_A_C || (left; exact BetS_B_A_C) || right).
Qed.

End Euclid.
