Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_Rectangle :
	forall A B C D,
	RightTriangle D A B ->
	RightTriangle A B C ->
	RightTriangle B C D ->
	RightTriangle C D A ->
	Cross A C B D ->
	Rectangle A B C D.
Proof.
	intros A B C D.
	intros RightTriangle_D_A_B.
	intros RightTriangle_A_B_C.
	intros RightTriangle_B_C_D.
	intros RightTriangle_C_D_A.
	intros Cross_A_C_B_D.

	unfold Rectangle.
	split.
	exact RightTriangle_D_A_B.
	split.
	exact RightTriangle_A_B_C.
	split.
	exact RightTriangle_B_C_D.
	split.
	exact RightTriangle_C_D_A.
	exact Cross_A_C_B_D.
Qed.

End Euclid.
