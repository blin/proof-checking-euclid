Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

(* Originally known as lemma_3_7b *)
Lemma lemma_orderofpoints_ABC_BCD_ABD :
	forall A B C D,
	BetS A B C -> BetS B C D ->
	BetS A B D.
Proof.
	intros A B C D.
	intros BetS_A_B_C.
	intros BetS_B_C_D.
	apply (axiom_betweennesssymmetry) in BetS_A_B_C as BetS_C_B_A.
	apply (axiom_betweennesssymmetry) in BetS_B_C_D as BetS_D_C_B.
	pose proof(lemma_orderofpoints_ABC_BCD_ACD D C B A BetS_D_C_B BetS_C_B_A) as BetS_D_B_A.
	apply (axiom_betweennesssymmetry) in BetS_D_B_A as BetS_A_B_D.
	exact BetS_A_B_D.
Qed.

End Euclid.


