Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma by_def_InCirc_center :
	forall J U V W,
	CI J U V W ->
	InCirc U J.
Proof.
	intros J U V W.
	intros CI_J_U_VW.
	unfold InCirc.
	exists U, U, U, V, W.
	split.
	exact CI_J_U_VW.
	left.
	reflexivity.
Qed.

End Euclid.
