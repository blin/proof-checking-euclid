Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_supp :
	forall A B C D F,
	OnRay B C D ->
	BetS A B F ->
	Supp A B C D F.
Proof.
	intros A B C D F.
	intros OnRay_BC_D.
	intros BetS_A_B_F.

	unfold Supp.
	split.
	exact OnRay_BC_D.
	exact BetS_A_B_F.
Qed.

End Euclid.
