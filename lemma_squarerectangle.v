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
	destruct Square_A_B_C_D_2 as (Cong_AB_CD & Cong_AB_BC & Cong_AB_DA & RightTriangle_DAB & RightTriangle_ABC & RightTriangle_BCD & RightTriangle_CDA).

	pose proof (lemma_squareparallelogram _ _ _ _ Square_A_B_C_D) as Parallelogram_A_B_C_D.
	pose proof (lemma_PGrectangle _ _ _ _ Parallelogram_A_B_C_D RightTriangle_DAB) as Rectangle_A_B_C_D.

	exact Rectangle_A_B_C_D.
Qed.

End Euclid.

