Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_extensionunique.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_s_lt.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_onray.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_crossbar : 
	forall A B C E U V,
	Triangle A B C ->
	BetS A E C ->
	OnRay B A U ->
	OnRay B C V ->
	exists X, OnRay B E X /\ BetS U X V.
Proof.
	intros A B C E U V.
	intros Triangle_A_B_C.
	intros BetS_A_E_C.
	intros OnRay_B_A_U.
	intros OnRay_B_C_V.

	assert (nCol A B C) as nCol_A_B_C by (unfold Triangle in Triangle_A_B_C; exact Triangle_A_B_C).
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.
	destruct nCol_A_B_C as (neq_A_B & neq_A_C & neq_B_C & nBetS_A_B_C & nBetS_A_C_B & nBetS_B_A_C).

	assert (~ eq B E) as neq_B_E.
	{
		intros eq_B_E.

		assert (BetS A B C) as BetS_A_B_C by (rewrite eq_B_E; exact BetS_A_E_C).

		contradict BetS_A_B_C.
		exact nBetS_A_B_C.
	}
	pose proof (lemma_inequalitysymmetric _ _ neq_B_E) as neq_E_B.

	pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.

	pose proof (lemma_onray_strict _ _ _ OnRay_B_A_U) as neq_B_U.
	pose proof (lemma_onray_strict _ _ _ OnRay_B_C_V) as neq_B_V.
	pose proof (lemma_extension _ _ _ _ neq_B_A neq_B_U) as (P & BetS_B_A_P & Cong_AP_BU).
	pose proof (lemma_extension _ _ _ _ neq_B_C neq_B_V) as (Q & BetS_B_C_Q & Cong_CQ_BV).

	assert (~ Col B Q A) as n_Col_B_Q_A.
	{
		intros Col_B_Q_A.

		pose proof (lemma_collinearorder _ _ _ Col_B_Q_A) as (Col_Q_B_A & _ & _ & _ & _).

		assert (Col B C Q) as Col_B_C_Q by (unfold Col; one_of_disjunct BetS_B_C_Q).
		pose proof (lemma_collinearorder _ _ _ Col_B_C_Q) as (_ & _ & Col_Q_B_C & _ & _).

		pose proof (lemma_betweennotequal _ _ _ BetS_B_C_Q) as (_ & _ & neq_B_Q).

		pose proof (lemma_inequalitysymmetric _ _ neq_B_Q) as neq_Q_B.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_B_A Col_Q_B_C neq_Q_B) as Col_B_A_C.
		pose proof (lemma_collinearorder _ _ _ Col_B_A_C) as (Col_A_B_C & _ & _ & _ & _).

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_B_Q_A) as nCol_B_Q_A.

	pose proof (postulate_Pasch_outer A B C E Q  BetS_A_E_C BetS_B_C_Q nCol_B_Q_A) as (F & BetS_A_F_Q & BetS_B_E_F).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_F_Q) as BetS_Q_F_A.

	assert (~ Col B P Q) as n_Col_B_P_Q.
	{
		intros Col_B_P_Q.

		pose proof (lemma_collinearorder _ _ _ Col_B_P_Q) as (Col_P_B_Q & _ & _ & _ & _).

		assert (Col B A P) as Col_B_A_P by (unfold Col; one_of_disjunct BetS_B_A_P).
		pose proof (lemma_collinearorder _ _ _ Col_B_A_P) as (_ & _ & Col_P_B_A & _ & _).

		pose proof (lemma_betweennotequal _ _ _ BetS_B_A_P) as (_ & _ & neq_B_P).

		pose proof (lemma_inequalitysymmetric _ _ neq_B_P) as neq_P_B.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_P_B_Q Col_P_B_A neq_P_B) as Col_B_Q_A.

		contradict Col_B_Q_A.
		exact n_Col_B_Q_A.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_B_P_Q) as nCol_B_P_Q.

	pose proof (lemma_NCorder _ _ _ nCol_B_P_Q) as (nCol_P_B_Q & nCol_P_Q_B & nCol_Q_B_P & nCol_B_Q_P & nCol_Q_P_B).

	pose proof (postulate_Pasch_outer Q B A F P BetS_Q_F_A BetS_B_A_P nCol_B_P_Q) as (W & BetS_Q_W_P & BetS_B_F_W).
	pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_B_E_F BetS_B_F_W) as BetS_B_E_W.
	destruct OnRay_B_A_U as (J & BetS_J_B_U & BetS_J_B_A).
	pose proof (cn_congruencereverse A P) as Cong_AP_PA.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AP_BU) as Cong_BU_AP.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_BU_AP Cong_AP_PA) as Cong_BU_PA.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BU_PA) as Cong_PA_BU.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_P) as BetS_P_A_B.
	pose proof (lemma_s_lt _ _ _ _ _ BetS_P_A_B Cong_PA_BU) as Lt_BU_PB.
	pose proof (cn_congruencereverse P B) as Cong_PB_BP.
	pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_BU_PB Cong_PB_BP) as Lt_BU_BP.
	destruct Lt_BU_BP as (S & BetS_B_S_P & Cong_BS_BU).
	pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_J_B_A BetS_B_A_P) as BetS_J_B_P.
	pose proof (axiom_orderofpoints_ABD_BCD_ABC J B S P BetS_J_B_P BetS_B_S_P) as BetS_J_B_S.
	pose proof (lemma_extensionunique _ _ _ _ BetS_J_B_S BetS_J_B_U Cong_BS_BU) as eq_S_U.
	assert (BetS B U P) as BetS_B_U_P by (rewrite <- eq_S_U; exact BetS_B_S_P).
	destruct OnRay_B_C_V as (K & BetS_K_B_V & BetS_K_B_C).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_CQ_BV) as Cong_BV_CQ.
	pose proof (cn_congruencereverse C Q) as Cong_CQ_QC.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_BV_CQ Cong_CQ_QC) as Cong_BV_QC.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BV_QC) as Cong_QC_BV.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_C_Q) as BetS_Q_C_B.
	pose proof (lemma_s_lt _ _ _ _ _ BetS_Q_C_B Cong_QC_BV) as Lt_BV_QB.
	pose proof (cn_congruencereverse Q B) as Cong_QB_BQ.
	pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_BV_QB Cong_QB_BQ) as Lt_BV_BQ.
	destruct Lt_BV_BQ as (R & BetS_B_R_Q & Cong_BR_BV).
	pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_K_B_C BetS_B_C_Q) as BetS_K_B_Q.
	pose proof (axiom_orderofpoints_ABD_BCD_ABC K B R Q BetS_K_B_Q BetS_B_R_Q) as BetS_K_B_R.
	pose proof (lemma_extensionunique _ _ _ _ BetS_K_B_R BetS_K_B_V Cong_BR_BV) as eq_R_V.
	assert (BetS B V Q) as BetS_B_V_Q by (rewrite <- eq_R_V; exact BetS_B_R_Q).

	pose proof (postulate_Pasch_inner Q B P W U BetS_Q_W_P BetS_B_U_P nCol_Q_P_B) as (M & BetS_Q_M_U & BetS_B_M_W).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_Q_M_U) as BetS_U_M_Q.

	assert (~ Col U Q B) as n_Col_U_Q_B.
	{
		intros Col_U_Q_B.

		pose proof (lemma_collinearorder _ _ _ Col_U_Q_B) as (_ & _ & Col_B_U_Q & _ & _).

		assert (Col B U P) as Col_B_U_P by (unfold Col; one_of_disjunct BetS_B_U_P).
		pose proof (lemma_collinearorder _ _ _ Col_B_U_P) as (Col_U_B_P & _ & _ & _ & _).

		pose proof (lemma_collinearorder _ _ _ Col_U_Q_B) as (_ & _ & _ & Col_U_B_Q & _).

		pose proof (lemma_inequalitysymmetric _ _ neq_B_U) as neq_U_B.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_U_B_P Col_U_B_Q neq_U_B) as Col_B_P_Q.
		pose proof (lemma_collinearorder _ _ _ Col_B_P_Q) as (_ & _ & _ & _ & Col_Q_P_B).

		contradict Col_B_P_Q.
		exact n_Col_B_P_Q.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_U_Q_B) as nCol_U_Q_B.

	pose proof (postulate_Pasch_inner U B Q M V BetS_U_M_Q BetS_B_V_Q nCol_U_Q_B) as (H & BetS_U_H_V & BetS_B_H_M).

	pose proof (lemma_extension _ _ _ _ neq_E_B neq_B_E) as (N & BetS_E_B_N & Cong_BN_BE).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_B_N) as BetS_N_B_E.
	pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_B_H_M BetS_B_M_W) as BetS_B_H_W.
	pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_N_B_E BetS_B_E_W) as BetS_N_B_W.
	pose proof (axiom_orderofpoints_ABD_BCD_ABC N B H W BetS_N_B_W BetS_B_H_W) as BetS_N_B_H.

	pose proof (lemma_s_onray _ _ _ _ BetS_N_B_E BetS_N_B_H) as OnRay_B_E_H.

	exists H.
	split.
	exact OnRay_B_E_H.
	exact BetS_U_H_V.
Qed.

End Euclid.
