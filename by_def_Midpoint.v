Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_Midpoint :
	forall A B C,
	BetS A B C ->
	Cong A B B C ->
	Midpoint A B C.
Proof.
	intros A B C.
	intros BetS_A_B_C.
	intros Cong_AB_BC.

	unfold Midpoint.
	split.
	exact BetS_A_B_C.
	exact Cong_AB_BC.
Qed.

End Euclid.
