Require Import ProofCheckingEuclid.by_def_Square.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_Square_flip :
	forall A B C D,
	Square A B C D ->
	Square B A D C.
Proof.
	intros A B C D.
	intros Square_A_B_C_D.

	destruct Square_A_B_C_D as (
		Cong_A_B_C_D & Cong_A_B_B_C & Cong_A_B_D_A & RightTriangle_D_A_B & RightTriangle_A_B_C & RightTriangle_B_C_D & RightTriangle_C_D_A
	).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_A_B_C_D) as (Cong_B_A_D_C & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_A_B_D_A) as (Cong_B_A_A_D & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_A_B_B_C) as (Cong_B_A_C_B & _ & _).

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_A_B_C) as RightTriangle_C_B_A.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_D_A_B) as RightTriangle_B_A_D.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_C_D_A) as RightTriangle_A_D_C.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_B_C_D) as RightTriangle_D_C_B.

	pose proof (
		by_def_Square
		_ _ _ _
		Cong_B_A_D_C Cong_B_A_A_D Cong_B_A_C_B RightTriangle_C_B_A RightTriangle_B_A_D RightTriangle_A_D_C RightTriangle_D_C_B
	) as Square_B_A_D_C.

	exact Square_B_A_D_C.
Qed.

End Euclid.

