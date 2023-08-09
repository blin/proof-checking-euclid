Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_LtA_from_InAngle :
	forall A B C D E F X,
	InAngle D E F X ->
	CongA A B C D E X ->
	LtA A B C D E F.
Proof.
	intros A B C D E F X.
	intros InAngle_DEF_X.
	intros CongA_ABC_DEX.

	destruct InAngle_DEF_X as (U & V & OnRay_ED_U & OnRay_EF_V & BetS_U_X_V).

	unfold LtA.
	exists U, X, V.
	split.
	exact BetS_U_X_V.
	split.
	exact OnRay_ED_U.
	split.
	exact OnRay_EF_V.
	exact CongA_ABC_DEX.
Qed.

End Euclid.
