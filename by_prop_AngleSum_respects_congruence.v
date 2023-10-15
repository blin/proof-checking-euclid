Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B .
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_SumTwoRT.
Require Import ProofCheckingEuclid.by_def_Supp.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_flip.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_OnRay_impliescollinear.
Require Import ProofCheckingEuclid.by_prop_OnRay_neq_A_C.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_oppositeside_onray_PABC_RQP_QABC.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_14.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_AngleSum_respects_congruence :
	forall A B C D E F P Q R a b c d e f p q r,
	AngleSum A B C D E F P Q R ->
	CongA A B C a b c ->
	CongA D E F d e f ->
	AngleSum a b c d e f p q r ->
	CongA P Q R p q r.
Proof.
	intros A B C D E F P Q R a b c d e f p q r.
	intros AngleSum_ABC_DEF_PQR.
	intros CongA_ABC_abc.
	intros CongA_DEF_def.
	intros AngleSum_abc_def_pqr.

	assert (eq P P) as eq_P_P by (reflexivity).
	assert (eq Q Q) as eq_Q_Q by (reflexivity).
	assert (eq q q) as eq_q_q by (reflexivity).

	destruct AngleSum_ABC_DEF_PQR as (S & CongA_ABC_PQS & CongA_DEF_SQR & BetS_P_S_R).

	pose proof (by_def_Col_from_eq_A_C P S P eq_P_P) as Col_P_S_P.

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ABC_PQS) as CongA_PQS_ABC.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_PQS_ABC CongA_ABC_abc) as CongA_PQS_abc.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_ABC_PQS) as nCol_P_Q_S.
	pose proof (by_prop_nCol_order _ _ _ nCol_P_Q_S) as (_ & _ & _ & nCol_P_S_Q & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_P_Q_S) as (_ & _ & _ & neq_Q_P & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_P_Q_S) as (_ & neq_Q_S & _ & _ & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_Q_P) as OnRay_QP_P.

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_DEF_SQR) as CongA_SQR_DEF.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_SQR_DEF CongA_DEF_def) as CongA_SQR_def.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_DEF_SQR) as nCol_S_Q_R.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_S_Q_R) as (_ & neq_Q_R & _ & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_S_Q_R) as (neq_S_Q & _ & _ & _ & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_Q_R) as OnRay_QR_R.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_P_S_R) as Col_P_S_R.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_P_S_R) as (_ & _ & neq_P_R).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_P_S_Q Col_P_S_P Col_P_S_R neq_P_R) as nCol_P_R_Q.
	pose proof (by_prop_nCol_order _ _ _ nCol_P_R_Q) as (_ & _ & _ & nCol_P_Q_R & _).

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_S_Q) as OnRay_SQ_Q.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_SQ_Q BetS_P_S_R) as Supp_PSQ_QSR.

	destruct AngleSum_abc_def_pqr as (s & CongA_abc_pqs & CongA_def_sqr & BetS_p_s_r).

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_PQS_abc CongA_abc_pqs) as CongA_PQS_pqs.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_abc_pqs) as nCol_p_q_s.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_p_q_s) as (_ & _ & _ & neq_q_p & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_p_q_s) as (_ & neq_q_s & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_q_p) as neq_p_q.

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_SQR_def CongA_def_sqr) as CongA_SQR_sqr.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_def_sqr) as nCol_s_q_r.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_s_q_r) as (_ & neq_q_r & _ & _ & _ & _).

	pose proof (lemma_layoff _ _ _ _ neq_q_p neq_Q_P) as (G & OnRay_qp_G & Cong_qG_QP).

	pose proof (by_def_Col_from_eq_B_C G q q eq_q_q) as Col_G_q_q.

	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_qp_G) as OnRay_qG_p.
	pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_qp_G) as Col_q_p_G.
	pose proof (by_prop_Col_order _ _ _ Col_q_p_G) as (_ & _ & Col_G_q_p & _ & _).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_qG_QP) as Cong_QP_qG.

	pose proof (lemma_layoff _ _ _ _ neq_q_s neq_Q_S) as (H & OnRay_qs_H & Cong_qH_QS).

	pose proof (by_def_Col_from_eq_A_C q H q eq_q_q) as Col_q_H_q.

	pose proof (by_prop_OnRay_neq_A_C _ _ _ OnRay_qs_H) as neq_q_H.
	pose proof (by_prop_neq_symmetric _ _ neq_q_H) as neq_H_q.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_H_q) as OnRay_Hq_q.
	pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_qs_H) as Col_q_s_H.
	pose proof (by_prop_Col_order _ _ _ Col_q_s_H) as (_ & _ & _ & Col_q_H_s & _).

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_PQS_pqs OnRay_qp_G OnRay_qs_H) as CongA_PQS_GqH.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_PQS_GqH) as nCol_G_q_H.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_PQS_GqH) as CongA_GqH_PQS.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_G_q_H Col_G_q_p Col_G_q_q neq_p_q) as nCol_p_q_H.
	pose proof (by_prop_nCol_order _ _ _ nCol_p_q_H) as (_ & nCol_q_H_p & _ & _ & _).

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_p_s_r Col_q_H_s nCol_q_H_p) as OppositeSide_p_qH_r.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_p_qH_r) as OppositeSide_r_qH_p.

	pose proof (proposition_04 _ _ _ _ _ _ Cong_qG_QP Cong_qH_QS CongA_GqH_PQS) as (Cong_GH_PS & _ & CongA_qHG_QSP).

	pose proof (by_prop_CongA_flip _ _ _ _ _ _ CongA_qHG_QSP) as CongA_GHq_PSQ.

	pose proof (lemma_layoff _ _ _ _ neq_q_r neq_Q_R) as (K & OnRay_qr_K & Cong_qK_QR).

	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_qr_K) as OnRay_qK_r.

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_qK_QR) as Cong_QR_qK.

	pose proof (lemma_oppositeside_onray_PABC_RQP_QABC _ _ _ _ _ _ OppositeSide_r_qH_p OnRay_qK_r Col_q_H_q) as OppositeSide_K_qH_p.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_K_qH_p) as OppositeSide_p_qH_K.
	pose proof (lemma_oppositeside_onray_PABC_RQP_QABC _ _ _ _ _ _ OppositeSide_p_qH_K OnRay_qG_p Col_q_H_q) as OppositeSide_G_qH_K.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_G_qH_K) as OppositeSide_K_qH_G.

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_SQR_sqr OnRay_qs_H OnRay_qr_K) as CongA_SQR_HqK.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_SQR_HqK) as CongA_HqK_SQR.

	pose proof (proposition_04 _ _ _ _ _ _ Cong_qH_QS Cong_qK_QR CongA_HqK_SQR) as (Cong_HK_SR & CongA_qHK_QSR & _).

	pose proof (by_def_SumTwoRT _ _ _ _ _ _ _ _ _ _ _ Supp_PSQ_QSR CongA_GHq_PSQ CongA_qHK_QSR) as SumTwoRT_GHq_qHK.

	pose proof (proposition_14 _ _ _ _ _ SumTwoRT_GHq_qHK OnRay_Hq_q OppositeSide_K_qH_G) as (_ & BetS_G_H_K).

	pose proof (cn_sumofparts _ _ _ _ _ _ Cong_GH_PS Cong_HK_SR BetS_G_H_K BetS_P_S_R) as Cong_GK_PR.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_GK_PR) as Cong_PR_GK.

	pose proof (
		by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_QP_P OnRay_QR_R OnRay_qp_G OnRay_qr_K Cong_QP_qG Cong_QR_qK Cong_PR_GK nCol_P_Q_R
	) as CongA_PQR_pqr.

	exact CongA_PQR_pqr.
Qed.

End Euclid.
