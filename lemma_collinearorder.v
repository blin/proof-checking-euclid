Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_BCA.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_BAC.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_collinearorder :
	forall A B C,
	Col A B C ->
	Col B A C /\ Col B C A /\ Col C A B /\ Col A C B /\ Col C B A.
Proof.
	intros A B C.
	intros Col_A_B_C.

	pose proof (lemma_collinear_ABC_BCA _ _ _ Col_A_B_C) as Col_B_C_A.
	pose proof (lemma_collinear_ABC_BCA _ _ _ Col_B_C_A) as Col_C_A_B.
	pose proof (lemma_collinear_ABC_BAC _ _ _ Col_A_B_C) as Col_B_A_C.
	pose proof (lemma_collinear_ABC_BCA _ _ _ Col_B_A_C) as Col_A_C_B.
	pose proof (lemma_collinear_ABC_BCA _ _ _ Col_A_C_B) as Col_C_B_A.

	repeat split.
	exact Col_B_A_C.
	exact Col_B_C_A.
	exact Col_C_A_B.
	exact Col_A_C_B.
	exact Col_C_B_A.
Qed.

End Euclid.
