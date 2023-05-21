Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
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

Lemma lemma_TogetherGreater_symmetric :
	forall A B C a b c,
	TogetherGreater A a B b C c ->
	TogetherGreater B b A a C c.
Proof.
	intros A B C a b c.
	intros TogetherGreater_A_a_B_b_C_c.

	destruct TogetherGreater_A_a_B_b_C_c as (H & BetS_A_a_H & Cong_a_H_B_b & Lt_C_c_A_H).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_a_H) as (neq_a_H & _ & _).
	pose proof (axiom_nocollapse _ _ _ _ neq_a_H Cong_a_H_B_b) as neq_B_b.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_a_H) as (_ & neq_A_a & _).
	pose proof (lemma_extension _ _ _ _ neq_B_b neq_A_a) as (F & BetS_B_b_F & Cong_b_F_A_a).
	pose proof (lemma_doublereverse _ _ _ _ Cong_b_F_A_a) as (Cong_a_A_F_b & _).
	
	pose proof (lemma_congruenceflip a A F b Cong_a_A_F_b) as (_ & Cong_A_a_F_b & _).
		
	pose proof (lemma_congruenceflip a H B b Cong_a_H_B_b) as (_ & _ & Cong_a_H_b_B).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_b_F) as BetS_F_b_B.
	epose proof (cn_sumofparts A _ H F _ B Cong_A_a_F_b Cong_a_H_b_B BetS_A_a_H BetS_F_b_B) as Cong_A_H_F_B.
	
	pose proof (lemma_congruenceflip A H F B Cong_A_H_F_B) as (_ & _ & Cong_A_H_B_F).

	pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_C_c_A_H Cong_A_H_B_F) as Lt_C_c_B_F.
	epose proof (lemma_s_TogetherGreater B b A a C c F BetS_B_b_F Cong_b_F_A_a Lt_C_c_B_F) as TogetherGreater_B_b_A_a_C_c.

	exact TogetherGreater_B_b_A_a_C_c.
Qed.

End Euclid.
