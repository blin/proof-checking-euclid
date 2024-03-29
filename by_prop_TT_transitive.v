Require Import ProofCheckingEuclid.by_def_OnRay.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_TT.
Require Import ProofCheckingEuclid.by_def_TogetherGreater.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_Lt_transitive.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_layoffunique.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_TT_transitive :
	forall A B C D E F G H P Q R S,
	TT A B C D E F G H ->
	TT E F G H P Q R S ->
	TT A B C D P Q R S.
Proof.
	intros A B C D E F G H P Q R S.
	intros TT_A_B_C_D_E_F_G_H.
	intros TT_E_F_G_H_P_Q_R_S.

	destruct TT_A_B_C_D_E_F_G_H as (K & BetS_E_F_K & Cong_FK_GH & TogetherGreater_AB_CD_EK).
	destruct TT_E_F_G_H_P_Q_R_S as (L & BetS_P_Q_L & Cong_QL_RS & TogetherGreater_EF_GH_PL).

	destruct TogetherGreater_AB_CD_EK as (J & BetS_A_B_J & Cong_BJ_CD & Lt_EK_AJ).
	destruct TogetherGreater_EF_GH_PL as (M & BetS_E_F_M & Cong_FM_GH & Lt_PL_EM).

	assert (eq K K) as eq_K_K by (reflexivity).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_F_K) as (neq_F_K & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_F_M) as (neq_F_M & _ & _).
	pose proof (by_def_OnRay _ _ _ _ BetS_E_F_K BetS_E_F_M) as OnRay_FK_M.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_F_K) as OnRay_FK_K.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_FM_GH) as Cong_GH_FM.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_FK_GH Cong_GH_FM) as Cong_FK_FM.
	pose proof (lemma_layoffunique _ _ _ _ OnRay_FK_K OnRay_FK_M Cong_FK_FM) as eq_K_M.

	assert (Lt P L E K) as Lt_PL_EK by (rewrite eq_K_M; exact Lt_PL_EM).

	pose proof (by_prop_Lt_transitive _ _ _ _ _ _ Lt_PL_EK Lt_EK_AJ) as Lt_PL_AJ.

	pose proof (by_def_TogetherGreater _ _ _ _ _ _ _ BetS_A_B_J Cong_BJ_CD Lt_PL_AJ) as TogetherGreater_AB_CD_PL.

	pose proof (by_def_TT _ _ _ _ _ _ _ _ _ BetS_P_Q_L Cong_QL_RS TogetherGreater_AB_CD_PL) as TT_A_B_C_D_P_Q_R_S.

	exact TT_A_B_C_D_P_Q_R_S.
Qed.

End Euclid.
