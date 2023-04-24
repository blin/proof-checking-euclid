Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_isosceles :
	forall A B C,
	Triangle A B C ->
	Cong A B A C ->
	isosceles A B C.
Proof.
	intros A B C.
	intros Triangle_A_B_C.
	intros Cong_A_B_A_C.

	unfold isosceles.
	split.
	exact Triangle_A_B_C.
	exact Cong_A_B_A_C.
Qed.

End Euclid.

