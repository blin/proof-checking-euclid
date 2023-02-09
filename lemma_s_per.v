Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_per :
	forall A B C X,
	BetS A B X ->
	Cong A B X B ->
	Cong A C X C ->
	neq B C ->
	Per A B C.
Proof.
	intros A B C X.
	intros BetS_A_B_X.
	intros Cong_AB_XB.
	intros Cong_AC_XC.
	intros neq_B_C.

	unfold Per.
	exists X.
	repeat split.
	exact BetS_A_B_X.
	exact Cong_AB_XB.
	exact Cong_AC_XC.
	exact neq_B_C.
Qed.

End Euclid.
