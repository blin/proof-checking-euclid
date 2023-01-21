Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABD_BCD_ACD.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_orderofpoints_ABC_ACD_ABD :
	forall A B C D,
	BetS A B C ->
	BetS A C D ->
	BetS A B D.
Proof.
	intros A B C D.
	intros BetS_A_B_C.
	intros BetS_A_C_D.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_C) as BetS_C_B_A.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_D) as BetS_D_C_A.
	pose proof (lemma_orderofpoints_ABD_BCD_ACD _ _ _ _ BetS_D_C_A BetS_C_B_A) as BetS_D_B_A.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_B_A) as BetS_A_B_D.
	exact BetS_A_B_D.
Qed.

End Euclid.


