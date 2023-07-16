Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_Col_from_BetS_A_C_B :
	forall A B C,
	BetS A C B ->
	Col A B C.
Proof.
	intros A B C.
	intros BetS_A_C_B.

	unfold Col.
	repeat (exact BetS_A_C_B || (left; exact BetS_A_C_B) || right).
Qed.

End Euclid.
