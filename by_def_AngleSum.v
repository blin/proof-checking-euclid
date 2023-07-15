Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_AngleSum :
	forall A B C D E F P Q R X,
	CongA A B C P Q X ->
	CongA D E F X Q R ->
	BetS P X R ->
	AngleSum A B C D E F P Q R.
Proof.
	intros A B C D E F P Q R X.
	intros CongA_ABC_PQX.
	intros CongA_DEF_XQR.
	intros BetS_P_X_R.

	unfold AngleSum.
	exists X.
	split.
	exact CongA_ABC_PQX.
	split.
	exact CongA_DEF_XQR.
	exact BetS_P_X_R.
Qed.

End Euclid.
