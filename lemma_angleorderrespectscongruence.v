Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_s_lt.
Require Import ProofCheckingEuclid.lemma_s_lta.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.proposition_03.
Require Import ProofCheckingEuclid.proposition_04.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_angleorderrespectscongruence : 
	forall A B C D E F P Q R,
	LtA A B C D E F ->
	CongA P Q R D E F ->
	LtA A B C P Q R.
Proof.
	intros A B C D E F P Q R.
	intros LtA_A_B_C_D_E_F.
	intros CongA_P_Q_R_D_E_F.

	destruct LtA_A_B_C_D_E_F as (G & H & J & BetS_G_H_J & OnRay_E_D_G & OnRay_E_F_J & CongA_A_B_C_D_E_H).
	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_P_Q_R_D_E_F) as (neq_P_Q & neq_Q_R & neq_P_R & neq_D_E & neq_E_F & neq_D_F).
	pose proof (lemma_inequalitysymmetric _ _ neq_P_Q) as neq_Q_P.
	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_A_B_C_D_E_H) as (neq_A_B & neq_B_C & neq_A_C & _ & neq_E_H & neq_D_H).
	pose proof (lemma_onray_strict _ _ _ OnRay_E_D_G) as neq_E_G.
	pose proof (lemma_layoff _ _ _ _ neq_Q_P neq_E_G) as (U & OnRay_Q_P_U & Cong_Q_U_E_G).
	pose proof (lemma_onray_strict _ _ _ OnRay_E_F_J) as neq_E_J.
	pose proof (lemma_layoff _ _ _ _ neq_Q_R neq_E_J) as (V & OnRay_Q_R_V & Cong_Q_V_E_J).
	pose proof (cn_congruencereflexive G H) as Cong_G_H_G_H.
	pose proof (lemma_s_lt _ _ _ _ _ BetS_G_H_J Cong_G_H_G_H) as Lt_G_H_G_J.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_P_Q_R_D_E_F) as CongA_D_E_F_P_Q_R.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ U V CongA_D_E_F_P_Q_R OnRay_Q_P_U OnRay_Q_R_V) as CongA_D_E_F_U_Q_V.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_D_E_F_U_Q_V) as CongA_U_Q_V_D_E_F.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ G J CongA_U_Q_V_D_E_F OnRay_E_D_G OnRay_E_F_J) as CongA_U_Q_V_G_E_J.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_U_Q_V_G_E_J) as CongA_G_E_J_U_Q_V.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_Q_U_E_G) as Cong_E_G_Q_U.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_Q_V_E_J) as Cong_E_J_Q_V.

	pose proof (proposition_04 _ _ _ _ _ _ Cong_E_G_Q_U Cong_E_J_Q_V CongA_G_E_J_U_Q_V) as (Cong_G_J_U_V & CongA_E_G_J_Q_U_V & CongA_E_J_G_Q_V_U).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_G_J_U_V) as Cong_U_V_G_J.
	pose proof (lemma_betweennotequal _ _ _ BetS_G_H_J) as (_ & _ & neq_G_J).
	pose proof (lemma_s_onray_assert_bets_AEB _ _ _ BetS_G_H_J neq_G_J) as OnRay_G_J_H.

	pose proof (proposition_03 _ _ _ _ _ _ Lt_G_H_G_J Cong_U_V_G_J) as (W & BetS_U_W_V & Cong_U_W_G_H).
	assert (eq H H) as eq_H_H by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB _ _ neq_E_H) as OnRay_E_H_H.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ G H CongA_A_B_C_D_E_H OnRay_E_D_G OnRay_E_H_H) as CongA_A_B_C_G_E_H.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_A_B_C_G_E_H) as nCol_G_E_H.
	pose proof (lemma_NCorder _ _ _ nCol_G_E_H) as (nCol_E_G_H & nCol_E_H_G & nCol_H_G_E & nCol_G_H_E & nCol_H_E_G).
	pose proof (lemma_betweennotequal _ _ _ BetS_U_W_V) as (_ & _ & neq_U_V).
	pose proof (lemma_s_onray_assert_bets_AEB _ _ _ BetS_U_W_V neq_U_V) as OnRay_U_V_W.

	pose proof (lemma_s_onray_assert_ABB _ _ neq_U_V) as OnRay_U_V_V.
	assert (eq Q Q) as eq_Q_Q by (reflexivity).
	assert (eq E E) as eq_E_E by (reflexivity).
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_D_E_F_U_Q_V) as nCol_U_Q_V.
	pose proof (lemma_NCdistinct _ _ _ nCol_U_Q_V) as (neq_U_Q & neq_Q_V & _ & neq_Q_U & neq_V_Q & neq_V_U).
	pose proof (lemma_NCdistinct _ _ _ nCol_G_E_H) as (neq_G_E & _ & neq_G_H & _ & neq_H_E & neq_H_G).
	pose proof (lemma_s_onray_assert_ABB _ _ neq_U_Q) as OnRay_U_Q_Q.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_G_E) as OnRay_G_E_E.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ Q W CongA_E_G_J_Q_U_V OnRay_U_Q_Q OnRay_U_V_W) as CongA_E_G_J_Q_U_W.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_E_G_J_Q_U_W) as CongA_Q_U_W_E_G_J.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_G_J) as OnRay_G_J_J.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ E H CongA_Q_U_W_E_G_J OnRay_G_E_E OnRay_G_J_H) as CongA_Q_U_W_E_G_H.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_Q_U_W_E_G_H) as CongA_E_G_H_Q_U_W.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_E_G_H_Q_U_W) as nCol_Q_U_W.
	pose proof (lemma_NCorder _ _ _ nCol_Q_U_W) as (nCol_U_Q_W & nCol_U_W_Q & nCol_W_Q_U & nCol_Q_W_U & nCol_W_U_Q).
	pose proof (lemma_NCdistinct _ _ _ nCol_Q_U_W) as (_ & neq_U_W & neq_Q_W & _ & neq_W_U & neq_W_Q).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_U_W_G_H) as Cong_G_H_U_W.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_E_G_Q_U) as (Cong_G_E_U_Q & _ & _).
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_Q_U_W) as CongA_Q_U_W_W_U_Q.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_E_G_H_Q_U_W CongA_Q_U_W_W_U_Q) as CongA_E_G_H_W_U_Q.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_H_G_E) as CongA_H_G_E_E_G_H.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_H_G_E_E_G_H CongA_E_G_H_W_U_Q) as CongA_H_G_E_W_U_Q.
	pose proof (proposition_04 _ _ _ _ _ _ Cong_G_H_U_W Cong_G_E_U_Q CongA_H_G_E_W_U_Q) as (Cong_H_E_W_Q & CongA_G_H_E_U_W_Q & CongA_G_E_H_U_Q_W).
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_B_C_G_E_H CongA_G_E_H_U_Q_W) as CongA_A_B_C_U_Q_W.
	assert (eq W W) as eq_W_W by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB _ _ neq_Q_W) as OnRay_Q_W_W.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_Q_P_U) as OnRay_Q_U_P.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ P W CongA_A_B_C_U_Q_W OnRay_Q_U_P OnRay_Q_W_W) as CongA_A_B_C_P_Q_W.

	epose proof (lemma_s_lta A B C P Q R _ W _ BetS_U_W_V OnRay_Q_P_U OnRay_Q_R_V CongA_A_B_C_P_Q_W) as LtA_ABC_PQR.

	exact LtA_ABC_PQR.
Qed.

End Euclid.
