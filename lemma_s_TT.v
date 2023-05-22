Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_TT :
	forall A B C D E F G H X,
	BetS E F X ->
	Cong F X G H ->
	TogetherGreater A B C D E X ->
	TT A B C D E F G H.
Proof.
	intros A B C D E F G H X.
	intros BetS_E_F_X.
	intros Cong_FX_GH.
	intros TogetherGreater_A_B_C_D_E_X.

	unfold TT.
	exists X.
	split.
	exact BetS_E_F_X.
	split.
	exact Cong_FX_GH.
	exact TogetherGreater_A_B_C_D_E_X.
Qed.

End Euclid.
