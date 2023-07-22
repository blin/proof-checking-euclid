Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma by_def_InCirc_within_radius :
	forall P J U V W X Y,
	CI J U V W ->
	BetS U Y X ->
	Cong U X V W ->
	Cong U P U Y ->
	InCirc P J.
Proof.
	intros P J U V W X Y.
	intros CI_J_U_VW.
	intros BetS_U_Y_X.
	intros Cong_UX_VW.
	intros Cong_UP_UY.
	unfold InCirc.
	exists X, Y, U, V, W.
	split.
	exact CI_J_U_VW.
	right.
	repeat split.
	exact BetS_U_Y_X.
	exact Cong_UX_VW.
	exact Cong_UP_UY.
Qed.

End Euclid.

