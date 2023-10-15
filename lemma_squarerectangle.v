Require Import ProofCheckingEuclid.by_def_Square.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_PGrectangle.
Require Import ProofCheckingEuclid.lemma_squareparallelogram.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_squarerectangle :
	forall A B C D,
	Square A B C D ->
	Rectangle A B C D.
Proof.
	intros A B C D.
	intros Square_A_B_C_D.
	
	assert (Square_A_B_C_D_2 := Square_A_B_C_D).
	destruct Square_A_B_C_D_2 as (Cong_A_B_C_D & Cong_A_B_B_C & Cong_A_B_D_A & RightTriangle_D_A_B & RightTriangle_A_B_C & RightTriangle_B_C_D & RightTriangle_C_D_A).

	pose proof (lemma_squareparallelogram _ _ _ _ Square_A_B_C_D) as Parallelogram_A_B_C_D.
	pose proof (lemma_PGrectangle _ _ _ _ Parallelogram_A_B_C_D RightTriangle_D_A_B) as Rectangle_A_B_C_D.

	exact Rectangle_A_B_C_D.
Qed.

End Euclid.

