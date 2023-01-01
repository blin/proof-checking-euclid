Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_outcirc_beyond_perimeter :
	forall P J U V W X,
	CI J U V W ->
	BetS U X P ->
	Cong U X V W ->
	OutCirc P J.
Proof.
	intros P J U V W X.
	intros CI_J_U_VW.
	intros BetS_U_X_P.
	intros Cong_UX_VW.
	unfold OutCirc.
	exists X, U, V, W.
	repeat split.
	exact CI_J_U_VW.
	exact BetS_U_X_P.
	exact Cong_UX_VW.
Qed.

End Euclid.


