Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_OppositeSide :
	forall P A B Q X,
	BetS P X Q ->
	Col A B X ->
	nCol A B P ->
	OppositeSide P A B Q.
Proof.
	intros P A B Q X.
	intros BetS_P_X_Q.
	intros Col_A_B_X.
	intros nCol_A_B_P.

	unfold OppositeSide.
	exists X.
	split.
	exact BetS_P_X_Q.
	split.
	exact Col_A_B_X.
	exact nCol_A_B_P.
Qed.

End Euclid.
