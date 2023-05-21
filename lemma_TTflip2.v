Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_lessthancongruence_smaller.
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
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_s_TT.
Require Import ProofCheckingEuclid.lemma_s_TogetherGreater.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_TTflip2 :
	forall A B C D E F G H,
	TT A B C D E F G H ->
	TT A B C D H G F E.
Proof.
	intros A B C D E F G H.
	intros TT_A_B_C_D_E_F_G_H.

	destruct TT_A_B_C_D_E_F_G_H as (J & BetS_E_F_J & Cong_F_J_G_H & TogetherGreater_A_B_C_D_E_J).
	destruct TogetherGreater_A_B_C_D_E_J as (K & BetS_A_B_K & Cong_B_K_C_D & Lt_E_J_A_K).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_F_J) as (neq_F_J & _ & _).
	pose proof (axiom_nocollapse _ _ _ _ neq_F_J Cong_F_J_G_H) as neq_G_H.
	pose proof (lemma_inequalitysymmetric _ _ neq_G_H) as neq_H_G.
	pose proof (lemma_betweennotequal _ _ _ BetS_E_F_J) as (_ & neq_E_F & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_E_F) as neq_F_E.
	pose proof (lemma_extension _ _ _ _ neq_H_G neq_F_E (* not real *)) as (L & BetS_H_G_L & Cong_G_L_F_E).
	
	pose proof (lemma_congruenceflip G L F E Cong_G_L_F_E) as (Cong_L_G_E_F & _ & _).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_F_J_G_H) as Cong_G_H_F_J.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_G_L) as BetS_L_G_H.
	epose proof (cn_sumofparts L G H E F J Cong_L_G_E_F Cong_G_H_F_J BetS_L_G_H BetS_E_F_J) as Cong_L_H_E_J.
	pose proof (cn_congruencereverse H L) as Cong_H_L_L_H.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_H_L_L_H Cong_L_H_E_J) as Cong_H_L_E_J.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_H_L_E_J) as Cong_E_J_H_L.
	pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_E_J_A_K Cong_E_J_H_L) as Lt_H_L_A_K.

	pose proof (lemma_s_TogetherGreater A B C D H L K BetS_A_B_K Cong_B_K_C_D Lt_H_L_A_K) as TogetherGreater_A_B_C_D_H_L.

	epose proof (lemma_s_TT A B C D H G F E L BetS_H_G_L Cong_G_L_F_E TogetherGreater_A_B_C_D_H_L) as TT_A_B_C_D_H_G_F_E.

	exact TT_A_B_C_D_H_G_F_E.
Qed.

End Euclid.
