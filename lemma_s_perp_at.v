Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_perp_at :
	forall P Q A B C X,
	Col P Q C ->
	Col A B C ->
	Col A B X ->
	RightTriangle X C P ->
	Perp_at P Q A B C.
Proof.
	intros P Q A B C X.
	intros Col_P_Q_C.
	intros Col_A_B_C.
	intros Col_A_B_X.
	intros RightTriangle_X_C_P.

	unfold Perp_at.
	exists X.
	repeat split.
	exact Col_P_Q_C.
	exact Col_A_B_C.
	exact Col_A_B_X.
	exact RightTriangle_X_C_P.
Qed.

End Euclid.
