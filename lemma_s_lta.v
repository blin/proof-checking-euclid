Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_lta :
	forall A B C D E F U X V,
	BetS U X V ->
	OnRay E D U ->
	OnRay E F V ->
	CongA A B C D E X ->
	LtA A B C D E F.
Proof.
	intros A B C D E F U X V.
	intros BetS_U_X_V.
	intros OnRay_E_D_U.
	intros OnRay_E_F_V.
	intros CongA_A_B_C_D_E_X.

	unfold LtA.
	exists U, X, V.
	split.
	exact BetS_U_X_V.
	split.
	exact OnRay_E_D_U.
	split.
	exact OnRay_E_F_V.
	exact CongA_A_B_C_D_E_X.
Qed.

End Euclid.

