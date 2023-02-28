Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_onray :
	forall A B C X,
	 BetS X A B ->
	 BetS X A C ->
	 OnRay A B C.
Proof.
	intros A B C X.
	intros BetS_X_A_B.
	intros BetS_X_A_C.

	unfold OnRay.
	exists X.
	split.
	exact BetS_X_A_C.
	exact BetS_X_A_B.
Qed.

End Euclid.
