Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_InAngle :
	forall A B C P X Y,
	OnRay B A X ->
	OnRay B C Y ->
	BetS X P Y ->
	InAngle A B C P.
Proof.
	intros A B C P X Y.
	intros OnRay_BA_X.
	intros OnRay_BC_Y.
	intros BetS_X_P_Y.

	unfold InAngle.
	exists X, Y.
	split.
	exact OnRay_BA_X.
	split.
	exact OnRay_BC_Y.
	exact BetS_X_P_Y.
Qed.

End Euclid.
