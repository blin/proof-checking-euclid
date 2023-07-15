Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_TarskiPar :
	forall A B C D,
	neq A B ->
	neq C D ->
	~ Meet A B C D ->
	SameSide C D A B ->
	TarskiPar A B C D.
Proof.
	intros A B C D.
	intros neq_A_B.
	intros neq_C_D.
	intros n_Meet_A_B_C_D.
	intros SameSide_C_D_AB.

	unfold TarskiPar.
	split.
	exact neq_A_B.
	split.
	exact neq_C_D.
	split.
	exact n_Meet_A_B_C_D.
	exact SameSide_C_D_AB.
Qed.

End Euclid.
