Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_tarski_par :
	forall A B C D,
	neq A B ->
	neq C D ->
	~ Meet A B C D ->
	SS C D A B ->
	TarksiPar A B C D.
Proof.
	intros A B C D.
	intros neq_A_B.
	intros neq_C_D.
	intros n_Meet_A_B_C_D.
	intros SS_C_D_A_B.

	unfold TarksiPar.
	split.
	exact neq_A_B.
	split.
	exact neq_C_D.
	split.
	exact n_Meet_A_B_C_D.
	exact SS_C_D_A_B.
Qed.

End Euclid.
