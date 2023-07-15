Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_betweennesspreserved.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearright.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_extensionunique.
Require Import ProofCheckingEuclid.lemma_pointreflectionisometry.
Require Import ProofCheckingEuclid.lemma_right_triangle_NC.
Require Import ProofCheckingEuclid.lemma_right_triangle_leg_change.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
Require Import ProofCheckingEuclid.lemma_rightreverse.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Midpoint.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.proposition_10.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

(* Points C and D are reflected across line AB. *)
Lemma lemma_linereflectionisometry :
	forall A B C D E F,
	RightTriangle B A C ->
	RightTriangle A B D ->
	BetS C A E ->
	BetS D B F ->
	Cong A C A E ->
	Cong B D B F ->
	Cong C D E F.
Proof.
	intros A B C D E F.
	intros RightTriangle_BAC.
	intros RightTriangle_ABD.
	intros BetS_C_A_E.
	intros BetS_D_B_F.
	intros Cong_AC_AE.
	intros Cong_BD_BF.

	pose proof (cn_congruencereflexive A C) as Cong_AC_AC.
	pose proof (cn_congruencereverse B F) as Cong_BF_FB.

	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_BAC) as RightTriangle_CAB.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_ABD) as RightTriangle_DBA.

	assert (RightTriangle_ABD2 := RightTriangle_ABD).
	destruct RightTriangle_ABD2 as (G & BetS_A_B_G & _ & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_G) as BetS_G_B_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_G) as (neq_B_G & neq_A_B & neq_A_G).
	pose proof (lemma_betweennotequal _ _ _ BetS_G_B_A) as (neq_B_A & neq_G_B & neq_G_A).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_A_E) as BetS_E_A_C.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_B_F) as BetS_F_B_D.
	pose proof (lemma_betweennotequal _ _ _ BetS_D_B_F) as (neq_B_F & neq_D_B & neq_D_F).
	pose proof (lemma_betweennotequal _ _ _ BetS_F_B_D) as (neq_B_D & neq_F_B & neq_F_D).

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_D_B_F) as Col_D_B_F.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_AC_AE) as (_ & Cong_CA_AE & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AC_AE) as Cong_AE_AC.
	pose proof (lemma_doublereverse _ _ _ _ Cong_CA_AE) as (Cong_EA_AC & _).

	pose proof (by_def_Midpoint _ _ _ BetS_E_A_C Cong_EA_AC) as Midpoint_E_A_C.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_BD_BF) as (_ & Cong_DB_BF & _).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_BD_BF Cong_BF_FB) as Cong_BD_FB.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_DB_BF) as Cong_BF_DB.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_BF_DB) as (_ & Cong_FB_DB & _).

	pose proof (proposition_10 _ _ neq_A_B) as (M & BetS_A_M_B & Cong_MA_MB).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_M_B) as BetS_B_M_A.

	pose proof (lemma_s_onray_assert_bets_AEB _ _ _ BetS_B_M_A neq_B_A) as OnRay_BA_M.
	pose proof (lemma_s_onray_assert_bets_AEB _ _ _ BetS_A_M_B neq_A_B) as OnRay_AB_M.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_MA_MB) as Cong_MB_MA.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_MB_MA) as (_ & Cong_BM_MA & _).
	pose proof (by_def_Midpoint _ _ _ BetS_B_M_A Cong_BM_MA) as Midpoint_B_M_A.

	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_DBA OnRay_BA_M) as RightTriangle_DBM.
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_CAB OnRay_AB_M) as RightTriangle_CAM.

	pose proof (lemma_collinearright _ _ _ _ RightTriangle_DBA Col_D_B_F neq_F_B) as RightTriangle_FBA.
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_FBA OnRay_BA_M) as RightTriangle_FBM.

	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_DBM) as nCol_D_B_M.
	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_FBM) as nCol_F_B_M.
	pose proof (lemma_NCdistinct _ _ _ nCol_D_B_M) as (_ & _ & neq_D_M & _ & _ & neq_M_D).
	pose proof (lemma_NCdistinct _ _ _ nCol_F_B_M) as (_ & _ & neq_F_M & _ & _ & neq_M_F).

	pose proof (lemma_rightreverse _ _ _ _ RightTriangle_CAM BetS_C_A_E Cong_CA_AE) as Cong_CM_EM.
	pose proof (lemma_rightreverse _ _ _ _ RightTriangle_DBM BetS_D_B_F Cong_DB_BF) as Cong_DM_FM.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_DM_FM) as Cong_FM_DM.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_CM_EM) as Cong_EM_CM.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_FM_DM) as (Cong_MF_MD & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_EM_CM) as (Cong_ME_MC & _ & _).

	pose proof (lemma_extension _ _ _ _ neq_D_M neq_M_D) as (R & BetS_D_M_R & Cong_MR_MD).
	pose proof (lemma_extension _ _ _ _ neq_F_M neq_M_F) as (Q & BetS_F_M_Q & Cong_MQ_MF).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_M_Q) as BetS_Q_M_F.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_M_R) as BetS_R_M_D.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_MR_MD) as Cong_MD_MR.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_MQ_MF) as Cong_MF_MQ.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_MQ_MF) as (Cong_QM_FM & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_MD_MR) as (_ & Cong_DM_MR & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_MF_MQ) as (_ & Cong_FM_MQ & _).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_FM_DM Cong_DM_MR) as Cong_FM_MR.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_QM_FM Cong_FM_DM) as Cong_QM_DM.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_QM_DM Cong_DM_MR) as Cong_QM_MR.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_QM_MR) as (_ & _ & Cong_QM_RM).

	pose proof (by_def_Midpoint _ _ _ BetS_D_M_R Cong_DM_MR) as Midpoint_D_M_R.
	pose proof (by_def_Midpoint _ _ _ BetS_F_M_Q Cong_FM_MQ) as Midpoint_F_M_Q.

	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_D_M_R Midpoint_B_M_A neq_D_B) as Cong_DB_RA.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_D_M_R Midpoint_F_M_Q neq_D_F) as Cong_DF_RQ.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_F_M_Q Midpoint_B_M_A neq_F_B) as Cong_FB_QA.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_FB_QA) as Cong_QA_FB.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_QA_FB Cong_FB_DB) as Cong_QA_DB.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_QA_DB Cong_DB_RA) as Cong_QA_RA.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_QA_RA) as (_ & _ & Cong_QA_AR).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_DF_RQ) as (Cong_FD_QR & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_DB_RA) as (Cong_BD_AR & _ & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BD_AR) as Cong_AR_BD.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_AR_BD Cong_BD_BF) as Cong_AR_BF.

	pose proof (lemma_betweennesspreserved _ _ _ _ _ _ Cong_FB_QA Cong_FD_QR Cong_BD_AR BetS_F_B_D) as BetS_Q_A_R.

	pose proof (by_def_Midpoint _ _ _ BetS_Q_A_R Cong_QA_AR) as Midpoint_Q_A_R.

	(* assert by cases *)
	assert (eq E Q \/ neq E Q) as [eq_E_Q|neq_E_Q] by (apply Classical_Prop.classic).
	{
		(* case eq_E_Q *)
		assert (Midpoint F M E) as Midpoint_F_M_E by (rewrite eq_E_Q; exact Midpoint_F_M_Q).
		assert (Cong F M M E) as Cong_FM_ME by (rewrite eq_E_Q; exact Cong_FM_MQ).
		assert (BetS F M E) as BetS_F_M_E by (rewrite eq_E_Q; exact BetS_F_M_Q).

		pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_F_M_E Midpoint_B_M_A neq_F_B) as Cong_FB_EA.
		pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_F_M_E Midpoint_D_M_R neq_F_D) as Cong_FD_ER.

		pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_DM_FM Cong_FM_ME) as Cong_DM_ME.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_DM_ME) as (_ & Cong_MD_ME & _).

		pose proof (lemma_congruenceflip _ _ _ _ Cong_FB_EA) as (Cong_BF_AE & _ & _).
		pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_AR_BF Cong_BF_AE) as Cong_AR_AE.
		pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_AR_AE Cong_AE_AC) as Cong_AR_AC.

		pose proof (lemma_betweennesspreserved _ _ _ _ _ _ Cong_FB_EA Cong_FD_ER Cong_BD_AR BetS_F_B_D) as BetS_E_A_R.

		pose proof (lemma_extensionunique _ _ _ _ BetS_E_A_R BetS_E_A_C Cong_AR_AC) as eq_R_C.
		assert (Cong F M M C) as Cong_FM_MC by (rewrite <- eq_R_C; exact Cong_FM_MR).
		assert (BetS C M D) as BetS_C_M_D by (rewrite <- eq_R_C; exact BetS_R_M_D).

		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_FM_MC) as Cong_MC_FM.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_MC_FM) as (_ & Cong_CM_FM & _).

		pose proof (cn_sumofparts _ _ _ _ _ _ Cong_CM_FM Cong_MD_ME BetS_C_M_D BetS_F_M_E) as Cong_CD_FE.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_CD_FE) as (_ & _ & Cong_CD_EF).

		exact Cong_CD_EF.
	}
	{
		(* case neq_E_Q *)
		pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_E_A_C Midpoint_Q_A_R neq_E_Q) as Cong_EQ_CR.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_EQ_CR) as (Cong_QE_RC & _ & _).

		(* △QME and △RMC are SSS congruent. *)
		(* △EMF and △CMD are SAS congruent. *)
		(* ∠QME is supplement to ∠EMF and ∠RMC is supplement to ∠CMD . *)
		(* △EMF ≅ △CMD implies that FE ≅ DC . *)
		pose proof (
			axiom_5_line
			Q M F E
			R M D C

			Cong_MF_MD
			Cong_QE_RC
			Cong_ME_MC
			BetS_Q_M_F
			BetS_R_M_D
			Cong_QM_RM
		) as Cong_EF_CD.
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_EF_CD) as Cong_CD_EF.

		exact Cong_CD_EF.
	}
Qed.

End Euclid.
