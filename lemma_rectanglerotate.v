Require Import ProofCheckingEuclid.by_def_Cross.
Require Import ProofCheckingEuclid.by_def_Rectangle.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_rectanglerotate :
	forall A B C D,
	Rectangle A B C D ->
	Rectangle B C D A.
Proof.
	intros A B C D.
	intros Rectangle_A_B_C_D.


	destruct Rectangle_A_B_C_D as (RightTriangle_DAB & RightTriangle_ABC & RightTriangle_BCD & RightTriangle_CDA & Cross_AC_BD).

	destruct Cross_AC_BD as (M & BetS_A_M_C & BetS_B_M_D).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_M_C) as BetS_C_M_A.
	pose proof (by_def_Cross _ _ _ _ _ BetS_B_M_D BetS_C_M_A) as Cross_BD_CA.
	pose proof (by_def_Rectangle _ _ _ _ RightTriangle_ABC RightTriangle_BCD RightTriangle_CDA RightTriangle_DAB Cross_BD_CA) as Rectangle_B_C_D_A.

	exact Rectangle_B_C_D_A.
Qed.

End Euclid.

