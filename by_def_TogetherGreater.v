Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_TogetherGreater :
	forall A B C D E F X,
	BetS A B X ->
	Cong B X C D ->
	Lt E F A X ->
	TogetherGreater A B C D E F.
Proof.
	intros A B C D E F X.
	intros BetS_A_B_X.
	intros Cong_BX_CD.
	intros Lt_EF_AX.

	unfold TogetherGreater.
	exists X.
	split.
	exact BetS_A_B_X.
	split.
	exact Cong_BX_CD.
	exact Lt_EF_AX.
Qed.

End Euclid.

