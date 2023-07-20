Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_RightTriangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_OnRay_orderofpoints_any.
Require Import ProofCheckingEuclid.by_prop_eq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_interior5.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_RightTriangle_leg_change :
	forall A B C D,
	RightTriangle A B C ->
	OnRay B C D ->
	RightTriangle A B D.
Proof.
	intros A B C D.
	intros RightTriangle_ABC.
	intros OnRay_BC_D.

	assert (RightTriangle_ABC2 := RightTriangle_ABC).
	destruct RightTriangle_ABC2 as (E & BetS_A_B_E & Cong_AB_EB & Cong_AC_EC & neq_B_C).

	pose proof (cn_congruencereflexive B C) as Cong_BC_BC.
	pose proof (cn_congruencereflexive C D) as Cong_CD_CD.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_EB) as (Cong_BA_BE & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AC_EC) as (Cong_CA_CE & _ & _).

	pose proof (by_prop_OnRay_orderofpoints_any _ _ _ OnRay_BC_D) as [BetS_B_D_C|[eq_C_D|BetS_B_C_D]].
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
		pose proof (by_prop_Cong_flip _ _ _ _ Cong_DA_DE) as (Cong_AD_ED & _ & _).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_B_D_C) as (_ & neq_B_D & _).

		pose proof (by_def_RightTriangle _ _ _ _ BetS_A_B_E Cong_AB_EB Cong_AD_ED neq_B_D) as RightTriangle_ABD.

		exact RightTriangle_ABD.
	}
	{
		(* case eq_C_D *)
		pose proof (by_prop_eq_symmetric _ _ eq_C_D) as eq_D_C.
		assert (RightTriangle A B D) as RightTriangle_ABD by (rewrite eq_D_C; exact RightTriangle_ABC).

		exact RightTriangle_ABD.
	}
	{
		(* case BetS_B_C_D *)
		pose proof (
			axiom_5_line
			B C D A
			B C D E
			Cong_CD_CD
			Cong_BA_BE
			Cong_CA_CE
			BetS_B_C_D
			BetS_B_C_D
			Cong_BC_BC
		) as Cong_AD_ED.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_B_C_D) as (_ & _ & neq_B_D).
		pose proof (by_def_RightTriangle _ _ _ _ BetS_A_B_E Cong_AB_EB Cong_AD_ED neq_B_D) as RightTriangle_ABD.

		exact RightTriangle_ABD.
	}
Qed.

End Euclid.
