Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B .
Require Import ProofCheckingEuclid.by_def_AngleSum.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_CongA.
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
Require Import ProofCheckingEuclid.by_prop_OnRay_assert.
Require Import ProofCheckingEuclid.by_prop_OnRay_impliescollinear.
Require Import ProofCheckingEuclid.by_prop_OnRay_neq_A_B.
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
	intros AngleSum_A_B_C_D_E_F_P_Q_R.
	intros CongA_A_B_C_a_b_c.
	intros CongA_D_E_F_d_e_f.
	intros AngleSum_a_b_c_d_e_f_p_q_r.

	assert (eq P P) as eq_P_P by (reflexivity).
	assert (eq Q Q) as eq_Q_Q by (reflexivity).
	assert (eq q q) as eq_q_q by (reflexivity).

	destruct AngleSum_A_B_C_D_E_F_P_Q_R as (S & CongA_A_B_C_P_Q_S & CongA_D_E_F_S_Q_R & BetS_P_S_R).

	pose proof (by_def_Col_from_eq_A_C P S P eq_P_P) as Col_P_S_P.

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_A_B_C_P_Q_S) as CongA_P_Q_S_A_B_C.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_P_Q_S_A_B_C CongA_A_B_C_a_b_c) as CongA_P_Q_S_a_b_c.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_A_B_C_P_Q_S) as nCol_P_Q_S.
	pose proof (by_prop_nCol_order _ _ _ nCol_P_Q_S) as (_ & _ & _ & nCol_P_S_Q & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_P_Q_S) as (_ & _ & _ & neq_Q_P & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_P_Q_S) as (_ & neq_Q_S & _ & _ & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B Q P neq_Q_P) as OnRay_Q_P_P.

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_D_E_F_S_Q_R) as CongA_S_Q_R_D_E_F.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_S_Q_R_D_E_F CongA_D_E_F_d_e_f) as CongA_S_Q_R_d_e_f.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_D_E_F_S_Q_R) as nCol_S_Q_R.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_S_Q_R) as (_ & neq_Q_R & _ & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_S_Q_R) as (neq_S_Q & _ & _ & _ & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B Q R neq_Q_R) as OnRay_Q_R_R.

	pose proof (by_def_Col_from_BetS_A_B_C P S R BetS_P_S_R) as Col_P_S_R.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_P_S_R) as (_ & _ & neq_P_R).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_P_S_Q Col_P_S_P Col_P_S_R neq_P_R) as nCol_P_R_Q.
	pose proof (by_prop_nCol_order _ _ _ nCol_P_R_Q) as (_ & _ & _ & nCol_P_Q_R & _).

	pose proof (by_def_OnRay_from_neq_A_B S Q neq_S_Q) as OnRay_S_Q_Q.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_S_Q_Q BetS_P_S_R) as Supp_P_S_Q_Q_R.

	destruct AngleSum_a_b_c_d_e_f_p_q_r as (s & CongA_a_b_c_p_q_s & CongA_d_e_f_s_q_r & BetS_p_s_r).

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_P_Q_S_a_b_c CongA_a_b_c_p_q_s) as CongA_P_Q_S_p_q_s.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_a_b_c_p_q_s) as nCol_p_q_s.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_p_q_s) as (_ & _ & _ & neq_q_p & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_p_q_s) as (_ & neq_q_s & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_q_p) as neq_p_q.

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_S_Q_R_d_e_f CongA_d_e_f_s_q_r) as CongA_S_Q_R_s_q_r.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_d_e_f_s_q_r) as nCol_s_q_r.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_s_q_r) as (_ & neq_q_r & _ & _ & _ & _).

	pose proof (lemma_layoff _ _ _ _ neq_q_p neq_Q_P) as (G & OnRay_q_p_G & Cong_q_G_Q_P).

	pose proof (by_def_Col_from_eq_B_C G q q eq_q_q) as Col_G_q_q.

	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_q_p_G) as OnRay_q_G_p.
	pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_q_p_G) as Col_q_p_G.
	pose proof (by_prop_Col_order _ _ _ Col_q_p_G) as (_ & _ & Col_G_q_p & _ & _).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_q_G_Q_P) as Cong_Q_P_q_G.

	pose proof (lemma_layoff _ _ _ _ neq_q_s neq_Q_S) as (H & OnRay_q_s_H & Cong_q_H_Q_S).

	pose proof (by_def_Col_from_eq_A_C q H q eq_q_q) as Col_q_H_q.

	pose proof (by_prop_OnRay_neq_A_C _ _ _ OnRay_q_s_H) as neq_q_H.
	pose proof (by_prop_neq_symmetric _ _ neq_q_H) as neq_H_q.
	pose proof (by_def_OnRay_from_neq_A_B H q neq_H_q) as OnRay_H_q_q.
	pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_q_s_H) as Col_q_s_H.
	pose proof (by_prop_Col_order _ _ _ Col_q_s_H) as (_ & _ & _ & Col_q_H_s & _).

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_P_Q_S_p_q_s OnRay_q_p_G OnRay_q_s_H) as CongA_P_Q_S_G_q_H.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_P_Q_S_G_q_H) as nCol_G_q_H.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_P_Q_S_G_q_H) as CongA_G_q_H_P_Q_S.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_G_q_H Col_G_q_p Col_G_q_q neq_p_q) as nCol_p_q_H.
	pose proof (by_prop_nCol_order _ _ _ nCol_p_q_H) as (_ & nCol_q_H_p & _ & _ & _).

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_p_s_r Col_q_H_s nCol_q_H_p) as OppositeSide_p_q_H_r.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_p_q_H_r) as OppositeSide_r_q_H_p.

	pose proof (proposition_04 _ _ _ _ _ _ Cong_q_G_Q_P Cong_q_H_Q_S CongA_G_q_H_P_Q_S) as (Cong_G_H_P_S & _ & CongA_q_H_G_Q_S_P).

	pose proof (by_prop_CongA_flip _ _ _ _ _ _ CongA_q_H_G_Q_S_P) as CongA_G_H_q_P_S_Q.

	pose proof (lemma_layoff _ _ _ _ neq_q_r neq_Q_R) as (K & OnRay_q_r_K & Cong_q_K_Q_R).

	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_q_r_K) as OnRay_q_K_r.

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_q_K_Q_R) as Cong_Q_R_q_K.

	pose proof (lemma_oppositeside_onray_PABC_RQP_QABC _ _ _ _ _ _ OppositeSide_r_q_H_p OnRay_q_K_r Col_q_H_q) as OppositeSide_K_q_H_p.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_K_q_H_p) as OppositeSide_p_q_H_K.
	pose proof (lemma_oppositeside_onray_PABC_RQP_QABC _ _ _ _ _ _ OppositeSide_p_q_H_K OnRay_q_G_p Col_q_H_q) as OppositeSide_G_q_H_K.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_G_q_H_K) as OppositeSide_K_q_H_G.

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_S_Q_R_s_q_r OnRay_q_s_H OnRay_q_r_K) as CongA_S_Q_R_H_q_K.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_S_Q_R_H_q_K) as CongA_H_q_K_S_Q_R.

	pose proof (proposition_04 _ _ _ _ _ _ Cong_q_H_Q_S Cong_q_K_Q_R CongA_H_q_K_S_Q_R) as (Cong_H_K_S_R & CongA_q_H_K_Q_S_R & _).

	pose proof (by_def_SumTwoRT _ _ _ _ _ _ _ _ _ _ _ Supp_P_S_Q_Q_R CongA_G_H_q_P_S_Q CongA_q_H_K_Q_S_R) as SumTwoRT_G_H_q_q_H_K.

	pose proof (proposition_14 _ _ _ _ _ SumTwoRT_G_H_q_q_H_K OnRay_H_q_q OppositeSide_K_q_H_G) as (_ & BetS_G_H_K).

	pose proof (cn_sumofparts _ _ _ _ _ _ Cong_G_H_P_S Cong_H_K_S_R BetS_G_H_K BetS_P_S_R) as Cong_G_K_P_R.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_G_K_P_R) as Cong_P_R_G_K.

	pose proof (
		by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_Q_P_P OnRay_Q_R_R OnRay_q_p_G OnRay_q_r_K Cong_Q_P_q_G Cong_Q_R_q_K Cong_P_R_G_K nCol_P_Q_R
	) as CongA_P_Q_R_p_q_r.

	exact CongA_P_Q_R_p_q_r.
Qed.

End Euclid.
