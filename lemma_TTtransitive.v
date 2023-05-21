Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_lessthantransitive.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_lt.
Require Import ProofCheckingEuclid.lemma_s_lta.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_onray.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_s_TogetherGreater.
Require Import ProofCheckingEuclid.lemma_s_TT.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_TTtransitive :
	forall A B C D E F G H P Q R S,
	TT A B C D E F G H ->
	TT E F G H P Q R S ->
	TT A B C D P Q R S.
Proof.
	intros A B C D E F G H P Q R S.
	intros TT_A_B_C_D_E_F_G_H.
	intros TT_E_F_G_H_P_Q_R_S.

	destruct TT_A_B_C_D_E_F_G_H as (K & BetS_E_F_K & Cong_F_K_G_H & TogetherGreater_A_B_C_D_E_K).
	destruct TogetherGreater_A_B_C_D_E_K as (J & BetS_A_B_J & Cong_B_J_C_D & Lt_E_K_A_J).
	destruct TT_E_F_G_H_P_Q_R_S as (L & BetS_P_Q_L & Cong_Q_L_R_S & TogetherGreater_E_F_G_H_P_L).
	destruct TogetherGreater_E_F_G_H_P_L as (M & BetS_E_F_M & Cong_F_M_G_H & Lt_P_L_E_M).
	assert (eq K K) as eq_K_K by (reflexivity).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_F_K) as (neq_F_K & _ & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_F_M) as (neq_F_M & _ & _).
	pose proof (lemma_s_onray _ _ _ _ BetS_E_F_K BetS_E_F_M) as OnRay_F_K_M.
	pose proof (lemma_s_onray_assert_ABB F K neq_F_K) as OnRay_F_K_K.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_F_M_G_H) as Cong_G_H_F_M.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_F_K_G_H Cong_G_H_F_M) as Cong_F_K_F_M.
	pose proof (lemma_layoffunique _ _ _ _ OnRay_F_K_K OnRay_F_K_M Cong_F_K_F_M) as eq_K_M.
	
	assert (Lt P L E K) as Lt_P_L_E_K by (rewrite eq_K_M; exact Lt_P_L_E_M).

	pose proof (lemma_lessthantransitive _ _ _ _ _ _ Lt_P_L_E_K Lt_E_K_A_J) as Lt_P_L_A_J.

	epose proof (lemma_s_TogetherGreater A B C D P L J BetS_A_B_J Cong_B_J_C_D Lt_P_L_A_J) as TogetherGreater_A_B_C_D_P_L.

	epose proof (lemma_s_TT A B C D P Q R S L BetS_P_Q_L Cong_Q_L_R_S TogetherGreater_A_B_C_D_P_L) as TT_A_B_C_D_P_Q_R_S.

	exact TT_A_B_C_D_P_Q_R_S.
Qed.

End Euclid.
