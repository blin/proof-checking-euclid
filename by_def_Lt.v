Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_Lt :
	forall A B C D X,
	BetS C X D ->
	Cong C X A B ->
	Lt A B C D.
Proof.
	intros A B C D X.
	intros BetS_C_X_D.
	intros Cong_CX_AB.

	unfold Lt.
	exists X.
	split.
	exact BetS_C_X_D.
	exact Cong_CX_AB.
Qed.

End Euclid.
