Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_interior5.
Require Import ProofCheckingEuclid.lemma_onray_orderofpoints_any.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.
Require Import ProofCheckingEuclid.lemma_s_right_triangle.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_right_triangle_leg_change : 
	forall A B C D,
	RightTriangle A B C ->
	OnRay B C D ->
	RightTriangle A B D.
Proof.
	intros A B C D.
	intros RightTriangle_A_B_C.
	intros OnRay_BC_D.

	assert (RightTriangle_A_B_C2 := RightTriangle_A_B_C).
	destruct RightTriangle_A_B_C2 as (E & BetS_A_B_E & Cong_AB_EB & Cong_AC_EC & neq_B_C).

	pose proof (cn_congruencereflexive B C) as Cong_BC_BC.
	pose proof (cn_congruencereflexive C D) as Cong_CD_CD.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AB_EB) as (Cong_BA_BE & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AC_EC) as (Cong_CA_CE & _ & _).

	pose proof (lemma_onray_orderofpoints_any _ _ _ OnRay_BC_D) as [BetS_B_D_C|[eq_C_D|BetS_B_C_D]].
	{
		(* case BetS_B_D_C *)
		pose proof (cn_congruencereflexive B D) as Cong_BD_BD.
		pose proof (cn_congruencereflexive D C) as Cong_DC_DC.
		pose proof (
			lemma_interior5
			_ D _ A
			_ D _ E
			BetS_B_D_C
			BetS_B_D_C
			Cong_BD_BD
			Cong_DC_DC
			Cong_BA_BE
			Cong_CA_CE
		) as Cong_DA_DE.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_DA_DE) as (Cong_AD_ED & _ & _).
		pose proof (lemma_betweennotequal _ _ _ BetS_B_D_C) as (_ & neq_B_D & _).

		pose proof (lemma_s_right_triangle _ _ _ _ BetS_A_B_E Cong_AB_EB Cong_AD_ED neq_B_D) as RightTriangle_A_B_D.

		exact RightTriangle_A_B_D.
	}
	{
		(* case eq_C_D *)
		pose proof (lemma_equalitysymmetric _ _ eq_C_D) as eq_D_C.
		assert (RightTriangle A B D) as RightTriangle_A_B_D by (rewrite eq_D_C; exact RightTriangle_A_B_C).

		exact RightTriangle_A_B_D.
	}
	{
		(* case BetS_B_C_D *)
		pose proof (
			axiom_5_line
			B C D A
			B C D E
			Cong_BC_BC
			Cong_CA_CE
			Cong_AB_EB

			BetS_B_C_D
			BetS_B_C_D

			Cong_AC_EC
			Cong_CD_CD
		) as Cong_DA_DE.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_DA_DE) as (Cong_AD_ED & _ & _).
		pose proof (lemma_betweennotequal _ _ _ BetS_B_C_D) as (_ & _ & neq_B_D).
		pose proof (lemma_s_right_triangle _ _ _ _ BetS_A_B_E Cong_AB_EB Cong_AD_ED neq_B_D) as RightTriangle_A_B_D.

		exact RightTriangle_A_B_D.
	}
Qed.

End Euclid.
