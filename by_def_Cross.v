Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_Cross :
	forall A B C D X,
	BetS A X B ->
	BetS C X D ->
	Cross A B C D.
Proof.
	intros A B C D X.
	intros BetS_A_X_B.
	intros BetS_C_X_D.

	unfold Cross.

	exists X.
	split.
	exact BetS_A_X_B.
	exact BetS_C_X_D.
Qed.

End Euclid.
