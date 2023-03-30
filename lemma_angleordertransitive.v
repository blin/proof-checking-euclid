Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_crossbar.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_neq_A_B.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_s_lta.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_angleordertransitive :
	forall A B C D E F P Q R,
	LtA A B C D E F ->
	LtA D E F P Q R ->
	LtA A B C P Q R.
Proof.
	intros A B C D E F P Q R.
	intros LtA_ABC_DEF.
	intros LtA_DEF_PQR.

	destruct LtA_DEF_PQR as (U & W & V & BetS_U_W_V & OnRay_QP_U & OnRay_QR_V & CongA_DEF_PQW).

	pose proof (lemma_onray_neq_A_B _ _ _ OnRay_QP_U) as neq_Q_P.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_QP_U) as OnRay_QU_P.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_Q_P) as OnRay_QP_P.

	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_QP_U) as Col_Q_P_U.
	pose proof (lemma_collinearorder _ _ _ Col_Q_P_U) as (_ & _ & Col_U_Q_P & _ & _).

	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_DEF_PQW) as (_ & _ & _ & _ & neq_Q_W & _).
	pose proof (lemma_s_onray_assert_ABB _ _ neq_Q_W) as OnRay_QW_W.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_DEF_PQW OnRay_QP_U OnRay_QW_W) as CongA_DEF_UQW.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_DEF_UQW) as CongA_UQW_DEF.
	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_ABC_DEF CongA_UQW_DEF) as LtA_ABC_UQW.
	destruct LtA_ABC_UQW as (S & H & T & BetS_S_H_T & OnRay_QU_S & OnRay_QW_T & CongA_ABC_UQH).

	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_QU_S) as Col_Q_U_S.
	pose proof (lemma_collinearorder _ _ _ Col_Q_U_S) as (Col_U_Q_S & _ & _ & _ & _).
	pose proof (lemma_onray_strict _ _ _ OnRay_QU_S) as neq_Q_S.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_QU_S) as OnRay_QS_U.

	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_QW_T) as OnRay_QT_W.

	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_ABC_UQH) as (_ & _ & _ & neq_U_Q & neq_Q_H & _).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_U_Q_S Col_U_Q_P neq_U_Q) as Col_Q_S_P.
	pose proof (lemma_collinearorder _ _ _ Col_Q_S_P) as (_ & _ & _ & Col_Q_P_S & _).
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_DEF_UQW OnRay_QU_P OnRay_QW_T) as CongA_DEF_PQT.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_DEF_PQT) as nCol_P_Q_T.
	pose proof (lemma_NCorder _ _ _ nCol_P_Q_T) as (nCol_Q_P_T & _ & _ & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_Q_P_T Col_Q_P_S neq_Q_S) as nCol_Q_S_T.
	pose proof (lemma_NCorder _ _ _ nCol_Q_S_T) as (nCol_S_Q_T & _ & _ & _ & _).
	assert (Triangle S Q T) as Triangle_SQT by (unfold Triangle; exact nCol_S_Q_T ).

	pose proof (lemma_s_onray_assert_ABB _ _ neq_Q_H) as OnRay_QH_H.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_ABC_UQH OnRay_QU_P OnRay_QH_H) as CongA_ABC_PQH.

	pose proof (lemma_crossbar _ _ _ _ _ _ Triangle_SQT BetS_S_H_T OnRay_QS_U OnRay_QT_W) as (K & OnRay_QH_K & BetS_U_K_W).
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_ABC_PQH OnRay_QP_P OnRay_QH_K) as CongA_ABC_PQK.
	pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_U_K_W BetS_U_W_V) as BetS_U_K_V.

	pose proof (lemma_s_lta _ _ _ _ _ _ _ _ _ BetS_U_K_V OnRay_QP_U OnRay_QR_V CongA_ABC_PQK) as LtA_ABC_PQR.

	exact LtA_ABC_PQR.
Qed.

End Euclid.
