Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_anglesum :
	forall A B C D E F P Q R X,
	CongA A B C P Q X ->
	CongA D E F X Q R ->
	BetS P X R ->
	AngleSum A B C D E F P Q R.
Proof.
	intros A B C D E F P Q R X.
	intros CongA_A_B_C_P_Q_X.
	intros CongA_D_E_F_X_Q_R.
	intros BetS_P_X_R.

	unfold AngleSum.
	exists X.
	split.
	exact CongA_A_B_C_P_Q_X.
	split.
	exact CongA_D_E_F_X_Q_R.
	exact BetS_P_X_R.
Qed.

End Euclid.
