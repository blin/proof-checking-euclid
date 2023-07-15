Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_SameSide :
	forall P Q A B X U V,
	Col A B U ->
	Col A B V ->
	BetS P U X ->
	BetS Q V X ->
	nCol A B P ->
	nCol A B Q ->
	SameSide P Q A B.
Proof.
	intros P Q A B X U V.
	intros Col_A_B_U.
	intros Col_A_B_V.
	intros BetS_P_U_X.
	intros BetS_Q_V_X.
	intros nCol_A_B_P.
	intros nCol_A_B_Q.

	exists X, U, V.
	split.
	exact Col_A_B_U.
	split.
	exact Col_A_B_V.
	split.
	exact BetS_P_U_X.
	split.
	exact BetS_Q_V_X.
	split.
	exact nCol_A_B_P.
	exact nCol_A_B_Q.
Qed.

End Euclid.
