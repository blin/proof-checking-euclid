Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_orderofpoints_ABD_BCD_ACD :
	forall A B C D,
	BetS A B D ->
	BetS B C D ->
	BetS A C D.
Proof.
	intros A B C D.
	intros BetS_A_B_D.
	intros BetS_B_C_D.
	pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_A_B_D BetS_B_C_D) as BetS_A_B_C.
	pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_A_B_C BetS_B_C_D) as BetS_A_C_D.
	exact BetS_A_C_D.
Qed.

End Euclid.


