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
		Cong_AB_CD & Cong_AB_BC & Cong_AB_DA & RightTriangle_DAB & RightTriangle_ABC & RightTriangle_BCD & RightTriangle_CDA
	).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_CD) as (Cong_BA_DC & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_DA) as (Cong_BA_AD & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_BC) as (Cong_BA_CB & _ & _).

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_ABC) as RightTriangle_CBA.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_DAB) as RightTriangle_BAD.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_CDA) as RightTriangle_ADC.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_BCD) as RightTriangle_DCB.

	pose proof (
		by_def_Square
		_ _ _ _
		Cong_BA_DC Cong_BA_AD Cong_BA_CB RightTriangle_CBA RightTriangle_BAD RightTriangle_ADC RightTriangle_DCB
	) as Square_B_A_D_C.

	exact Square_B_A_D_C.
Qed.

End Euclid.

