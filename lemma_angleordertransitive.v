Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_crossbar.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_neq_A_B.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_s_lta.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.proposition_04.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_angleordertransitive : 
	forall A B C D E F P Q R,
	LtA A B C D E F ->
	LtA D E F P Q R ->
	LtA A B C P Q R.
Proof.
	intros A B C D E F P Q R.
	intros LtA_A_B_C_D_E_F.
	intros LtA_D_E_F_P_Q_R.

	destruct LtA_D_E_F_P_Q_R as (U & W & V & BetS_U_W_V & OnRay_Q_P_U & OnRay_Q_R_V & CongA_D_E_F_P_Q_W).
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_D_E_F_P_Q_W) as CongA_P_Q_W_D_E_F.
	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_D_E_F_P_Q_W) as (neq_D_E & neq_E_F & neq_D_F & neq_P_Q & neq_Q_W & neq_P_W).
	pose proof (lemma_inequalitysymmetric _ _ neq_D_E) as neq_E_D.
	pose proof (lemma_onray_strict _ _ _ OnRay_Q_P_U) as neq_Q_U.
	pose proof (lemma_layoff _ _ _ _ neq_E_D neq_Q_U) as (G & OnRay_E_D_G & Cong_EG_QU).
	pose proof (lemma_layoff _ _ _ _ neq_E_F neq_Q_W) as (J & OnRay_E_F_J & Cong_EJ_QW).
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_P_Q_W_D_E_F) as nCol_D_E_F.
	pose proof (lemma_equalanglesreflexive _ _ _ nCol_D_E_F) as CongA_D_E_F_D_E_F.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ G J CongA_D_E_F_D_E_F OnRay_E_D_G OnRay_E_F_J) as CongA_D_E_F_G_E_J.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_D_E_F_G_E_J) as CongA_G_E_J_D_E_F.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_G_E_J_D_E_F CongA_D_E_F_P_Q_W) as CongA_G_E_J_P_Q_W.
	assert (eq W W) as eq_W_W by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB _ _ neq_Q_W) as OnRay_Q_W_W.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ U W CongA_G_E_J_P_Q_W OnRay_Q_P_U OnRay_Q_W_W) as CongA_G_E_J_U_Q_W.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_D_E_F_G_E_J) as nCol_G_E_J.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_G_E_J_U_Q_W) as nCol_U_Q_W.
	assert (Triangle G E J) as Triangle_G_E_J by (unfold Triangle; exact nCol_G_E_J ).
	assert (Triangle U Q W) as Triangle_U_Q_W by (unfold Triangle; exact nCol_U_Q_W ).
	pose proof (proposition_04 E G J Q U W Cong_EG_QU Cong_EJ_QW CongA_G_E_J_U_Q_W) as (Cong_G_J_U_W & _ & _).
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ U W CongA_D_E_F_P_Q_W OnRay_Q_P_U OnRay_Q_W_W) as CongA_D_E_F_U_Q_W.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_D_E_F_U_Q_W) as CongA_U_Q_W_D_E_F.
	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_A_B_C_D_E_F CongA_U_Q_W_D_E_F) as LtA_A_B_C_U_Q_W.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_Q_P_U) as OnRay_Q_U_P.
	destruct LtA_A_B_C_U_Q_W as (S & H & T & BetS_S_H_T & OnRay_Q_U_S & OnRay_Q_W_T & CongA_A_B_C_U_Q_H).
	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_A_B_C_U_Q_H) as (neq_A_B & neq_B_C & neq_A_C & neq_U_Q & neq_Q_H & neq_U_H).
	assert (eq H H) as eq_H_H by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB _ _ neq_Q_H) as OnRay_Q_H_H.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_A_B_C_U_Q_H OnRay_Q_U_P OnRay_Q_H_H) as CongA_A_B_C_P_Q_H.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ P T CongA_D_E_F_U_Q_W OnRay_Q_U_P OnRay_Q_W_T) as CongA_D_E_F_P_Q_T.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_D_E_F_P_Q_T) as nCol_P_Q_T.
	assert (Triangle P Q T) as Triangle_P_Q_T by (unfold Triangle; exact nCol_P_Q_T ).
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_P_Q_T) as n_Col_P_Q_T.
	pose proof (lemma_onray_neq_A_B _ _ _ OnRay_Q_P_U) as neq_Q_P.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_Q_W_T) as OnRay_Q_T_W.

	assert (~ Col S Q T) as n_Col_S_Q_T.
	{
		intros Col_S_Q_T.

		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_Q_U_S) as Col_Q_U_S.
		pose proof (lemma_collinearorder _ _ _ Col_Q_U_S) as (Col_U_Q_S & _ & _ & _ & _).

		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_Q_P_U) as Col_Q_P_U.
		pose proof (lemma_collinearorder _ _ _ Col_Q_P_U) as (_ & _ & Col_U_Q_P & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_U_Q_S Col_U_Q_P neq_U_Q) as Col_Q_S_P.
		pose proof (lemma_collinearorder _ _ _ Col_Q_S_P) as (Col_S_Q_P & _ & _ & _ & _).

		pose proof (lemma_onray_strict _ _ _ OnRay_Q_U_S) as neq_Q_S.
		pose proof (lemma_inequalitysymmetric _ _ neq_Q_S) as neq_S_Q.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_S_Q_T Col_S_Q_P neq_S_Q) as Col_Q_T_P.
		pose proof (lemma_collinearorder _ _ _ Col_Q_T_P) as (_ & _ & Col_P_Q_T & _ & _).

		contradict Col_P_Q_T.
		exact n_Col_P_Q_T.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_S_Q_T) as nCol_S_Q_T.

	assert (Triangle S Q T) as Triangle_S_Q_T by (unfold Triangle; exact nCol_S_Q_T ).
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_Q_U_S) as OnRay_Q_S_U.
	pose proof (lemma_crossbar _ _ _ _ _ _ Triangle_S_Q_T BetS_S_H_T OnRay_Q_S_U OnRay_Q_T_W) as (K & OnRay_Q_H_K & BetS_U_K_W).
	pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_U_K_W BetS_U_W_V) as BetS_U_K_V.
	assert (eq P P) as eq_P_P by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB _ _ neq_Q_P) as OnRay_Q_P_P.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ P K CongA_A_B_C_P_Q_H OnRay_Q_P_P OnRay_Q_H_K) as CongA_A_B_C_P_Q_K.

	epose proof (lemma_s_lta A B C P Q R _ K _ BetS_U_K_V OnRay_Q_P_U OnRay_Q_R_V CongA_A_B_C_P_Q_K) as LtA_ABC_PQR.

	exact LtA_ABC_PQR.
Qed.

End Euclid.
