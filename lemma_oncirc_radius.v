Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_oncirc_radius :
	forall B J U X Y,
	CI J U X Y ->
	Cong U B X Y ->
	OnCirc B J.
Proof.
	intros B J U X Y.
	intros CI_J_U_XY.
	intros Cong_UB_XY.
	unfold OnCirc.
	exists X, Y, U.
	split.
	exact CI_J_U_XY.
	exact Cong_UB_XY.
Qed.

End Euclid.

