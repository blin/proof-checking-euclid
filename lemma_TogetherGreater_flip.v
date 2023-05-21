Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
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
Require Import ProofCheckingEuclid.lemma_s_TogetherGreater.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_TogetherGreater_flip :
	forall A B C a b c,
	TogetherGreater A a B b C c ->
	TogetherGreater a A B b C c /\ TogetherGreater A a B b c C.
Proof.
	intros A B C a b c.
	intros TogetherGreater_A_a_B_b_C_c.

	destruct TogetherGreater_A_a_B_b_C_c as (H & BetS_A_a_H & Cong_a_H_B_b & Lt_C_c_A_H).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_a_H) as (_ & neq_A_a & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_a) as neq_a_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_a_H) as (neq_a_H & _ & _).
	pose proof (axiom_nocollapse _ _ _ _ neq_a_H Cong_a_H_B_b) as neq_B_b.
	pose proof (lemma_extension _ _ _ _ neq_a_A neq_B_b (* not real *)) as (h & BetS_a_A_h & Cong_A_h_B_b).
	pose proof (cn_congruencereverse A a) as Cong_A_a_a_A.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_A_h_B_b) as Cong_B_b_A_h.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_a_H_B_b Cong_B_b_A_h) as Cong_a_H_A_h.
	epose proof (cn_sumofparts A a H a A h Cong_A_a_a_A Cong_a_H_A_h BetS_A_a_H BetS_a_A_h) as Cong_A_H_a_h.
	pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_C_c_A_H Cong_A_H_a_h) as Lt_C_c_a_h.

	epose proof (lemma_s_TogetherGreater a A B b C c h BetS_a_A_h Cong_A_h_B_b Lt_C_c_a_h) as TogetherGreater_a_A_B_b_C_c.
	pose proof (cn_congruencereverse C c) as Cong_C_c_c_C.
	pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_C_c_A_H Cong_C_c_c_C) as Lt_c_C_A_H.

	pose proof (lemma_s_TogetherGreater A a B b c C H BetS_A_a_H Cong_a_H_B_b Lt_c_C_A_H) as TogetherGreater_A_a_B_b_c_C.

	split.
	exact TogetherGreater_a_A_B_b_C_c.
	exact TogetherGreater_A_a_B_b_c_C.
Qed.

End Euclid.
