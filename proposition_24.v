Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence_smaller.
Require Import ProofCheckingEuclid.lemma_angleordertransitive.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_crossbar.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalanglesflip.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_lessthancongruence_smaller.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_neq_A_B.
Require Import ProofCheckingEuclid.lemma_onray_orderofpoints_any.
Require Import ProofCheckingEuclid.lemma_onray_shared_initial_point.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_isosceles.
Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.by_def_LtA.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_05.
Require Import ProofCheckingEuclid.proposition_16.
Require Import ProofCheckingEuclid.proposition_19.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_24 :
	forall A B C D E F,
	Triangle A B C ->
	Triangle D E F ->
	Cong A B D E ->
	Cong A C D F ->
	LtA E D F B A C ->
	Lt E F B C.
Proof.
	intros A B C D E F.
	intros Triangle_ABC.
	intros Triangle_DEF.
	intros Cong_AB_DE.
	intros Cong_AC_DF.
	intros LtA_EDF_BAC.

	pose proof (lemma_s_ncol_triangle _ _ _ Triangle_ABC) as nCol_A_B_C.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).


	destruct LtA_EDF_BAC as (P & T & Q & BetS_P_T_Q & OnRay_AB_P & OnRay_AC_Q & CongA_EDF_BAT).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_T_Q) as BetS_Q_T_P.

	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_AC_Q) as OnRay_AQ_C.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_AB_P) as OnRay_AP_B.
	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_AQ_C) as Col_A_Q_C.
	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_AP_B) as Col_A_P_B.

	pose proof (lemma_collinearorder _ _ _ Col_A_Q_C) as (Col_Q_A_C & Col_Q_C_A & Col_C_A_Q & Col_A_C_Q & Col_C_Q_A).
	pose proof (lemma_collinearorder _ _ _ Col_A_P_B) as (Col_P_A_B & Col_P_B_A & Col_B_A_P & Col_A_B_P & Col_B_P_A).

	pose proof (lemma_onray_strict _ _ _ OnRay_AB_P) as neq_A_P.
	pose proof (lemma_onray_neq_A_B _ _ _ OnRay_AQ_C) as neq_A_Q.
	pose proof (lemma_inequalitysymmetric _ _ neq_A_P) as neq_P_A.
	pose proof (lemma_inequalitysymmetric _ _ neq_A_Q) as neq_Q_A.

	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_EDF_BAT) as nCol_B_A_T.

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_B_A_T) as n_Col_B_A_T.
	pose proof (lemma_NCdistinct _ _ _ nCol_B_A_T) as (_ & neq_A_T & neq_B_T & _ & neq_T_A & neq_T_B).
	pose proof (lemma_NCorder _ _ _ nCol_B_A_T) as (nCol_A_B_T & nCol_A_T_B & nCol_T_B_A & nCol_B_T_A & nCol_T_A_B).

	pose proof (lemma_layoff _ _ _ _ neq_A_T neq_A_C) as (H & OnRay_AT_H & Cong_AH_AC).

	pose proof (lemma_onray_strict _ _ _ OnRay_AT_H) as neq_A_H.
	pose proof (lemma_inequalitysymmetric _ _ neq_A_H) as neq_H_A.

	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_AT_H) as Col_A_T_H.
	pose proof (lemma_collinearorder _ _ _ Col_A_T_H) as (Col_T_A_H & Col_T_H_A & Col_H_A_T & Col_A_H_T & Col_H_T_A).

	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_AH_AC Cong_AC_DF) as Cong_AH_DF.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AH_AC) as Cong_AC_AH.

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_T_B Col_A_T_H neq_A_H) as nCol_A_H_B.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_H_B) as (_ & neq_H_B & _ & _ & _ & _).
	pose proof (lemma_NCorder _ _ _ nCol_A_H_B) as (nCol_H_A_B & nCol_H_B_A & nCol_B_A_H & nCol_A_B_H & nCol_B_H_A).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_C_B Col_A_C_Q neq_A_Q) as nCol_A_Q_B.
	pose proof (lemma_NCorder _ _ _ nCol_A_Q_B) as (nCol_Q_A_B & nCol_Q_B_A & nCol_B_A_Q & nCol_A_B_Q & nCol_B_Q_A).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_B_Q Col_A_B_P neq_A_P) as nCol_A_P_Q.
	pose proof (lemma_NCorder _ _ _ nCol_A_P_Q) as (nCol_P_A_Q & nCol_P_Q_A & nCol_Q_A_P & nCol_A_Q_P & nCol_Q_P_A).

	pose proof (by_def_Triangle _ _ _ nCol_Q_A_P) as Triangle_QAP.

	pose proof (lemma_crossbar _ _ _ _ _ _ Triangle_QAP BetS_Q_T_P OnRay_AQ_C OnRay_AP_B) as (J & OnRay_AT_J & BetS_C_J_B).

	pose proof (lemma_onray_strict _ _ _ OnRay_AT_J) as neq_A_J.
	pose proof (lemma_betweennotequal _ _ _ BetS_C_J_B) as (_ & neq_C_J & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_C_J) as neq_J_C.

	pose proof (lemma_onray_shared_initial_point _ _ _ _ OnRay_AT_J OnRay_AT_H) as OnRay_AJ_H.
	pose proof (lemma_s_onray_assert_bets_AEB _ _ _ BetS_C_J_B neq_C_B) as OnRay_CB_J.
	pose proof (lemma_s_onray_assert_bets_ABE _ _ _ BetS_C_J_B neq_C_J) as OnRay_CJ_B.

	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_AJ_H) as Col_A_J_H.
	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_AT_J) as Col_A_T_J.
	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_C_J_B) as Col_C_J_B.

	pose proof (lemma_collinearorder _ _ _ Col_A_J_H) as (Col_J_A_H & Col_J_H_A & Col_H_A_J & Col_A_H_J & Col_H_J_A).
	pose proof (lemma_collinearorder _ _ _ Col_A_T_J) as (Col_T_A_J & Col_T_J_A & Col_J_A_T & Col_A_J_T & Col_J_T_A).
	pose proof (lemma_collinearorder _ _ _ Col_C_J_B) as (Col_J_C_B & Col_J_B_C & Col_B_C_J & Col_C_B_J & Col_B_J_C).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_H_B Col_A_H_J neq_A_J) as nCol_A_J_B.
	pose proof (lemma_NCorder _ _ _ nCol_A_J_B) as (nCol_J_A_B & nCol_J_B_A & nCol_B_A_J & nCol_A_B_J & nCol_B_J_A).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_J_B_A Col_J_B_C neq_J_C) as nCol_J_C_A.
	pose proof (lemma_NCorder _ _ _ nCol_J_C_A) as (nCol_C_J_A & nCol_C_A_J & nCol_A_J_C & nCol_J_A_C & nCol_A_C_J).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_J_C Col_A_J_H neq_A_H) as nCol_A_H_C.
	pose proof (lemma_NCorder _ _ _ nCol_A_H_C) as (nCol_H_A_C & nCol_H_C_A & nCol_C_A_H & nCol_A_C_H & nCol_C_H_A).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_H_C) as (_ & neq_H_C & _ & _ & neq_C_H & _).
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_C_H) as n_Col_A_C_H.

	pose proof (by_def_Triangle _ _ _ nCol_C_A_H) as Triangle_CAH.

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_H_C) as CongA_AHC_CHA.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_C_H) as CongA_ACH_HCA.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq H H) as eq_H_H by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB _ _ neq_A_B) as OnRay_AB_B.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_C_A) as OnRay_CA_A.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_C_H) as OnRay_CH_H.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_H_B) as OnRay_HB_B.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_H_C) as OnRay_HC_C.
	pose proof (cn_congruencereverse B C) as Cong_BC_CB.
	pose proof (cn_congruencereverse B H) as Cong_BH_HB.
	pose proof (cn_congruencereverse C B) as Cong_CB_BC.
	pose proof (cn_congruencereverse F E) as Cong_FE_EF.

	pose proof (by_def_Triangle _ _ _ nCol_A_C_H) as Triangle_ACH.
	pose proof (by_def_isosceles _ _ _ Triangle_ACH Cong_AC_AH) as isosceles_A_C_H.
	pose proof (proposition_05 _ _ _ isosceles_A_C_H) as CongA_ACH_AHC.

	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_EDF_BAT OnRay_AB_B OnRay_AT_H) as CongA_EDF_BAH.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_EDF_BAH) as CongA_BAH_EDF.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_ACH_AHC) as CongA_AHC_ACH.
	pose proof (lemma_equalanglesflip _ _ _ _ _ _ CongA_BAH_EDF) as CongA_HAB_FDE.

	pose proof (proposition_04 _ _ _ _ _ _ Cong_AH_DF Cong_AB_DE CongA_HAB_FDE) as (Cong_HB_FE & _ & _).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_HB_FE Cong_FE_EF) as Cong_HB_EF.

	(* assert by cases *)
	assert (Lt H B C B) as Lt_HB_CB.
	pose proof (lemma_onray_orderofpoints_any _ _ _ OnRay_AJ_H) as [BetS_A_H_J | [eq_J_H | BetS_A_J_H]].
	{
		(* case BetS_A_H_J *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_H_J) as BetS_J_H_A.
		pose proof (lemma_betweennotequal _ _ _ BetS_A_H_J) as (neq_H_J & _ & _).

		pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_H_A_C Col_H_A_J neq_H_J) as nCol_H_J_C.
		pose proof (lemma_NCorder _ _ _ nCol_H_J_C) as (nCol_J_H_C & nCol_J_C_H & nCol_C_H_J & nCol_H_C_J & nCol_C_J_H).

		pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_C_J_H Col_C_J_B neq_C_B) as nCol_C_B_H.
		pose proof (lemma_NCorder _ _ _ nCol_C_B_H) as (nCol_B_C_H & nCol_B_H_C & nCol_H_C_B & nCol_C_H_B & nCol_H_B_C).

		pose proof (by_def_Triangle _ _ _ nCol_B_H_C) as Triangle_BHC.
		pose proof (by_def_Triangle _ _ _ nCol_C_J_H) as Triangle_CJH.

		pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_H_C) as CongA_BHC_CHB.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_H_C_J) as CongA_HCJ_JCH.
		pose proof (lemma_equalanglesreflexive _ _ _ nCol_C_H_J) as CongA_CHJ_CHJ.
		pose proof (lemma_equalanglesreflexive _ _ _ nCol_H_C_J) as CongA_HCJ_HCJ.

		pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_HCJ_HCJ OnRay_CH_H OnRay_CJ_B) as CongA_HCJ_HCB.
		pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_HCJ_HCB) as CongA_HCB_HCJ.

		pose proof (proposition_16 _ _ _ _ Triangle_CJH BetS_J_H_A) as (LtA_JCH_CHA & _).
		pose proof (proposition_16 _ _ _ _ Triangle_CAH BetS_A_H_J) as (LtA_ACH_CHJ & _).

		pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_C_J_B OnRay_HC_C OnRay_HB_B CongA_CHJ_CHJ) as LtA_CHJ_CHB.
		pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_JCH_CHA CongA_HCJ_JCH) as LtA_HCJ_CHA.
		pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_HCJ_CHA CongA_AHC_CHA) as LtA_HCJ_AHC.
		pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_HCJ_AHC CongA_ACH_AHC) as LtA_HCJ_ACH.
		pose proof (lemma_angleordertransitive _ _ _ _ _ _ _ _ _ LtA_HCJ_ACH LtA_ACH_CHJ) as LtA_HCJ_CHJ.
		pose proof (lemma_angleordertransitive _ _ _ _ _ _ _ _ _ LtA_HCJ_CHJ LtA_CHJ_CHB) as LtA_HCJ_CHB.
		pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_HCJ_CHB CongA_HCB_HCJ) as LtA_HCB_CHB.
		pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_HCB_CHB CongA_BHC_CHB) as LtA_HCB_BHC.

		pose proof (proposition_19 _ _ _ Triangle_BHC LtA_HCB_BHC) as Lt_BH_BC.

		pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_BH_BC Cong_BH_HB) as Lt_HB_BC.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_HB_BC Cong_BC_CB) as Lt_HB_CB.

		exact Lt_HB_CB.
	}
	{
		(* case eq_J_H *)

		assert (BetS C H B) as BetS_C_H_B by (rewrite <- eq_J_H; exact BetS_C_J_B).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_H_B) as BetS_B_H_C.
		pose proof (by_def_Lt _ _ _ _ _ BetS_B_H_C Cong_BH_HB) as Lt_HB_BC.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_HB_BC Cong_BC_CB) as Lt_HB_CB.

		exact Lt_HB_CB.
	}
	{
		(* case BetS_A_J_H *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_J_H) as BetS_H_J_A.
		pose proof (lemma_betweennotequal _ _ _ BetS_A_J_H) as (neq_J_H & _ & _).
		pose proof (lemma_inequalitysymmetric _ _ neq_J_H) as neq_H_J.

		pose proof (lemma_s_onray_assert_bets_AEB _ _ _ BetS_H_J_A neq_H_A) as OnRay_HA_J.

		pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_H_A_C Col_H_A_J neq_H_J) as nCol_H_J_C.
		pose proof (lemma_NCorder _ _ _ nCol_H_J_C) as (nCol_J_H_C & nCol_J_C_H & nCol_C_H_J & nCol_H_C_J & nCol_C_J_H).

		pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_C_J_H Col_C_J_B neq_C_B) as nCol_C_B_H.
		pose proof (lemma_NCorder _ _ _ nCol_C_B_H) as (nCol_B_C_H & nCol_B_H_C & nCol_H_C_B & nCol_C_H_B & nCol_H_B_C).

		pose proof (by_def_Triangle _ _ _ nCol_B_H_C) as Triangle_BHC.

		pose proof (lemma_equalanglesreflexive _ _ _ nCol_H_C_B) as CongA_HCB_HCB.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_C_H) as CongA_BCH_HCB.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_H_C) as CongA_BHC_CHB.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_H_C_B) as CongA_HCB_BCH.

		pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_HCB_HCB OnRay_CH_H OnRay_CB_J) as CongA_HCB_HCJ.
		pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_AHC_CHA OnRay_HC_C OnRay_HA_J) as CongA_AHC_CHJ.

		pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_H_J_A OnRay_CH_H OnRay_CA_A CongA_HCB_HCJ) as LtA_HCB_HCA.
		pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_C_J_B OnRay_HC_C OnRay_HB_B CongA_AHC_CHJ) as LtA_AHC_CHB.

		pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_HCB_HCA CongA_BCH_HCB) as LtA_BCH_HCA.
		pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_BCH_HCA CongA_ACH_HCA) as LtA_BCH_ACH.
		pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_BCH_ACH CongA_AHC_ACH) as LtA_BCH_AHC.
		pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_AHC_CHB CongA_BHC_CHB) as LtA_AHC_BHC.
		pose proof (lemma_angleordertransitive _ _ _ _ _ _ _ _ _ LtA_BCH_AHC LtA_AHC_BHC) as LtA_BCH_BHC.
		pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_BCH_BHC CongA_HCB_BCH) as LtA_HCB_BHC.

		pose proof (proposition_19 _ _ _ Triangle_BHC LtA_HCB_BHC) as Lt_BH_BC.

		pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_BH_BC Cong_BH_HB) as Lt_HB_BC.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_HB_BC Cong_BC_CB) as Lt_HB_CB.

		exact Lt_HB_CB.
	}

	pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_HB_CB Cong_HB_EF) as Lt_EF_CB.
	pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_EF_CB Cong_CB_BC) as Lt_EF_BC.

	exact Lt_EF_BC.
Qed.

End Euclid.
