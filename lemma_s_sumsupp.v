Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_sumsupp :
	forall A B C D E F X Y Z U V,
	Supp X Y U V Z ->
	CongA A B C X Y U ->
	CongA D E F V Y Z ->
	SumSupp A B C D E F.
Proof.
	intros A B C D E F X Y Z U V.
	intros Supp_XYU_VYZ.
	intros CongA_ABC_XYU.
	intros CongA_DEF_VYZ.
	unfold SumSupp.
	exists X, Y, Z, U, V.
	split.
	exact Supp_XYU_VYZ.
	split.
	exact CongA_ABC_XYU.
	exact CongA_DEF_VYZ.
Qed.

End Euclid.
