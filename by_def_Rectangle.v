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
	intros RightTriangle_DAB.
	intros RightTriangle_ABC.
	intros RightTriangle_BCD.
	intros RightTriangle_CDA.
	intros Cross_AC_BD.

	unfold Rectangle.
	split.
	exact RightTriangle_DAB.
	split.
	exact RightTriangle_ABC.
	split.
	exact RightTriangle_BCD.
	split.
	exact RightTriangle_CDA.
	exact Cross_AC_BD.
Qed.

End Euclid.
