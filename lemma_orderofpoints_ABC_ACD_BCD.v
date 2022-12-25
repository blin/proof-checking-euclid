Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral}.

(* Originally known as lemma_3_6a *)
Lemma lemma_orderofpoints_ABC_ACD_BCD :
	forall A B C D,
	BetS A B C -> BetS A C D ->
	BetS B C D.
Proof.
	intros A B C D.
	intros BetS_A_B_C.
	intros BetS_A_C_D.
	apply (axiom_betweennesssymmetry) in BetS_A_B_C as BetS_C_B_A.
	apply (axiom_betweennesssymmetry) in BetS_A_C_D as BetS_D_C_A.
	pose proof (axiom_orderofpoints_ABD_BCD_ABC D C B A BetS_D_C_A BetS_C_B_A) as BetS_D_C_B.
	apply (axiom_betweennesssymmetry) in BetS_D_C_B as BetS_B_C_D.
	exact BetS_B_C_D.
Qed.

End Euclid.

