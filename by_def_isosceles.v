Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_isosceles :
	forall A B C,
	Triangle A B C ->
	Cong A B A C ->
	isosceles A B C.
Proof.
	intros A B C.
	intros Triangle_ABC.
	intros Cong_AB_AC.

	unfold isosceles.
	split.
	exact Triangle_ABC.
	exact Cong_AB_AC.
Qed.

End Euclid.

