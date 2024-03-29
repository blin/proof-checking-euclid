Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Cong_doublereverse.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_OnRay_orderofpoints_any.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_differenceofparts.
Require Import ProofCheckingEuclid.lemma_extensionunique.
Require Import ProofCheckingEuclid.lemma_interior5.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_partnotequalwhole.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_layoffunique :
	forall A B C D,
	OnRay A B C ->
	OnRay A B D ->
	Cong A C A D->
	eq C D.
Proof.
	intros A B C D.
	intros OnRay_AB_C.
	intros OnRay_AB_D.
	intros Cong_AC_AD.

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AC_AD) as Cong_AD_AC.
	pose proof (cn_congruencereflexive A B) as Cong_AB_AB.
	pose proof (cn_congruencereflexive B C) as Cong_BC_BC.
	pose proof (cn_congruencereflexive A C) as Cong_AC_AC.

	pose proof (
		by_prop_OnRay_orderofpoints_any _ _ _ OnRay_AB_C
	) as BetS_A_C_B_or_eq_B_C_or_BetS_A_B_C.
	pose proof (
		by_prop_OnRay_orderofpoints_any _ _ _ OnRay_AB_D
	) as BetS_A_D_B_or_eq_B_D_or_BetS_A_B_D.

	destruct BetS_A_C_B_or_eq_B_C_or_BetS_A_B_C as [BetS_A_C_B | [eq_B_C | BetS_A_B_C]].
	{
		(* case BetS_A_C_B *)
		destruct BetS_A_D_B_or_eq_B_D_or_BetS_A_B_D as [BetS_A_D_B | [eq_B_D | BetS_A_B_D]].
		{
			(* case BetS_A_D_B *)
			pose proof (
				lemma_differenceofparts _ _ _ _ _ _ Cong_AC_AD Cong_AB_AB BetS_A_C_B BetS_A_D_B
			) as Cong_CB_DB.
			pose proof (by_prop_Cong_flip _ _ _ _ Cong_CB_DB) as (Cong_BC_BD & _ & _).
			pose proof (
				lemma_interior5
				_ _ _ _
				_ _ _ _
				BetS_A_C_B
				BetS_A_D_B
				Cong_AC_AD
				Cong_CB_DB
				Cong_AC_AC
				Cong_BC_BC
			) as Cong_CC_DC.
			assert (~ neq C D) as n_neq_C_D.
			{
				intros neq_C_D.

				pose proof (by_prop_Cong_doublereverse _ _ _ _ Cong_CC_DC) as (Cong_CD_CC & _).
				pose proof (axiom_nocollapse _ _ _ _ neq_C_D Cong_CD_CC) as neq_C_C.
				unfold neq in neq_C_C.
				assert (eq C C) as eq_C_C by (reflexivity).

				contradict eq_C_C.
				exact neq_C_C.
			}
			unfold neq in n_neq_C_D.
			apply Classical_Prop.NNPP in n_neq_C_D.
			exact n_neq_C_D.
		}
		{
			(* case eq_B_D *)
			assert (BetS A C D) as BetS_A_C_D by (rewrite <- eq_B_D; exact BetS_A_C_B).
			assert (~ neq C D) as n_neq_C_D.
			{
				intros neq_C_D.

				pose proof (lemma_partnotequalwhole _ _ _ BetS_A_C_D) as n_Cong_AC_AD.

				contradict n_Cong_AC_AD.
				exact Cong_AC_AD.
			}
			unfold neq in n_neq_C_D.
			apply Classical_Prop.NNPP in n_neq_C_D.
			exact n_neq_C_D.
		}
		{
			(* case BetS_A_B_D *)
			pose proof (
				lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_A_C_B BetS_A_B_D
			) as BetS_A_C_D.
			assert (~ neq C D) as n_neq_C_D.
			{
				intros neq_C_D.

				pose proof (lemma_partnotequalwhole _ _ _ BetS_A_C_D) as n_Cong_AC_AD.

				contradict n_Cong_AC_AD.
				exact Cong_AC_AD.
			}
			unfold neq in n_neq_C_D.
			apply Classical_Prop.NNPP in n_neq_C_D.
			exact n_neq_C_D.
		}
	}
	{
		(* case eq_B_C *)
		assert (Cong A B A D) as Cong_AB_AD by (rewrite eq_B_C; exact Cong_AC_AD).
		pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AB_AD) as Cong_AD_AB.
		destruct BetS_A_D_B_or_eq_B_D_or_BetS_A_B_D as [BetS_A_D_B | [eq_B_D | BetS_A_B_D]].
		{
			(* case BetS_A_D_B *)
			pose proof (lemma_partnotequalwhole _ _ _ BetS_A_D_B) as n_Cong_AD_AB.

			contradict n_Cong_AD_AB.
			exact Cong_AD_AB.
		}
		{
			(* case eq_B_D *)
			assert (eq C D) as eq_C_D by (rewrite <- eq_B_C; exact eq_B_D).
			exact eq_C_D.
		}
		{
			(* case BetS_A_B_D *)
			assert (BetS A C D) as BetS_A_C_D by (rewrite <- eq_B_C; exact BetS_A_B_D).
			assert (~ neq C D) as n_neq_C_D.
			{
				intros neq_C_D.

				pose proof (lemma_partnotequalwhole _ _ _ BetS_A_C_D) as n_Cong_AC_AD.

				contradict n_Cong_AC_AD.
				exact Cong_AC_AD.
			}
			unfold neq in n_neq_C_D.
			apply Classical_Prop.NNPP in n_neq_C_D.
			exact n_neq_C_D.
		}
	}
	{
		(* case BetS_A_B_C *)
		destruct BetS_A_D_B_or_eq_B_D_or_BetS_A_B_D as [BetS_A_D_B | [eq_B_D | BetS_A_B_D]].
		{
			(* case BetS_A_D_B *)
			pose proof (
				lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_A_D_B BetS_A_B_C
			) as BetS_A_D_C.
			assert (~ neq C D) as n_neq_C_D.
			{
				intros neq_C_D.

				pose proof (lemma_partnotequalwhole _ _ _ BetS_A_D_C) as n_Cong_AD_AC.

				contradict n_Cong_AD_AC.
				exact Cong_AD_AC.
			}
			unfold neq in n_neq_C_D.
			apply Classical_Prop.NNPP in n_neq_C_D.
			exact n_neq_C_D.
		}
		{
			(* case eq_B_D *)
			assert (BetS A D C) as BetS_A_D_C by (rewrite <- eq_B_D; exact BetS_A_B_C).
			assert (~ neq C D) as n_neq_C_D.
			{
				intros neq_C_D.

				pose proof (lemma_partnotequalwhole _ _ _ BetS_A_D_C) as n_Cong_AD_AC.

				contradict n_Cong_AD_AC.
				exact Cong_AD_AC.
			}
			unfold neq in n_neq_C_D.
			apply Classical_Prop.NNPP in n_neq_C_D.
			exact n_neq_C_D.
		}
		{
			(* case BetS_A_B_D *)
			pose proof (by_prop_BetS_notequal _ _ _ BetS_A_B_D) as (_ & neq_A_B & _).
			pose proof (
				lemma_differenceofparts _ _ _ _ _ _ Cong_AB_AB Cong_AC_AD BetS_A_B_C BetS_A_B_D
			) as Cong_BC_BD.
			pose proof (lemma_extensionunique _ _ _ _ BetS_A_B_C BetS_A_B_D Cong_BC_BD) as eq_C_D.
			exact eq_C_D.
		}
	}
Qed.

End Euclid.
