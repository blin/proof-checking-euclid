Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_LtA :
	forall A B C D E F U X V,
	BetS U X V ->
	OnRay E D U ->
	OnRay E F V ->
	CongA A B C D E X ->
	LtA A B C D E F.
Proof.
	intros A B C D E F U X V.
	intros BetS_U_X_V.
	intros OnRay_ED_U.
	intros OnRay_EF_V.
	intros CongA_ABC_DEX.

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

