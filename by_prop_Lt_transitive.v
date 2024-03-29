Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_OnRay_orderofpoints_any.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_Lt_transitive :
	forall A B C D E F,
	Lt A B C D ->
	Lt C D E F ->
	Lt A B E F.
Proof.

	intros A B C D E F.
	intros Lt_AB_CD.
	intros Lt_CD_EF.

	destruct Lt_AB_CD as (G & BetS_C_G_D & Cong_CG_AB).
	destruct Lt_CD_EF as (H & BetS_E_H_F & Cong_EH_CD).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_H_F) as (_ & neq_E_H & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_G_D) as (neq_G_D & neq_C_G & neq_C_D).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_EH_CD) as Cong_CD_EH.

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_C_G_D neq_C_G) as OnRay_CG_D.
	pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_C_G_D neq_C_D) as OnRay_CD_G.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_G) as OnRay_CG_G.

	pose proof (lemma_layoff _ _ _ _ neq_E_H neq_C_G) as (K & OnRay_EH_K & Cong_EK_CG).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_EK_CG) as Cong_CG_EK.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_EK_CG Cong_CG_AB) as Cong_EK_AB.
	pose proof (by_prop_OnRay_orderofpoints_any _ _ _ OnRay_EH_K) as BetS_E_K_H_or_eq_H_K_or_BetS_E_H_K.

	assert (BetS E K H) as BetS_E_K_H.
	destruct BetS_E_K_H_or_eq_H_K_or_BetS_E_H_K as [BetS_E_K_H|[eq_H_K|BetS_E_H_K]].
	{
		(* case BetS_E_K_H *)
		exact BetS_E_K_H.
	}
	{
		(* case eq_H_K *)
		assert (Cong C G E H) as Cong_CG_EH by (rewrite eq_H_K; exact Cong_CG_EK).

		pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_CG_EH Cong_EH_CD) as Cong_CG_CD.
		pose proof (lemma_layoffunique _ _ _ _ OnRay_CG_G OnRay_CG_D Cong_CG_CD) as eq_G_D.

		contradict eq_G_D.
		exact neq_G_D.
	}
	{
		(* case BetS_E_H_K *)
		pose proof (by_prop_BetS_notequal _ _ _ BetS_E_H_K) as (neq_H_K & _ & _).
		pose proof (lemma_extension _ _ _ _ neq_C_D neq_H_K) as (J & BetS_C_D_J & Cong_DJ_HK).
		pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_C_D_J neq_C_D) as OnRay_CD_J.
		pose proof (cn_sumofparts _ _ _ _ _ _ Cong_CD_EH Cong_DJ_HK BetS_C_D_J BetS_E_H_K) as Cong_CJ_EK.
		pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_CJ_EK Cong_EK_CG) as Cong_CJ_CG.
		pose proof (lemma_layoffunique _ _ _ _ OnRay_CD_J OnRay_CD_G Cong_CJ_CG) as eq_J_G.

		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_C_G_D BetS_C_D_J) as BetS_G_D_J.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_G_D_J) as (_ & _ & neq_G_J).
		pose proof (by_prop_neq_symmetric _ _ neq_G_J) as neq_J_G.

		contradict eq_J_G.
		exact neq_J_G.
	}

	pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_E_K_H BetS_E_H_F) as BetS_E_K_F.
	pose proof (by_def_Lt _ _ _ _ _ BetS_E_K_F Cong_EK_AB) as Lt_AB_EF.

	exact Lt_AB_EF.
Qed.

End Euclid.
