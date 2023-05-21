Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_differenceofparts.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_lessthanadditive.
Require Import ProofCheckingEuclid.lemma_lessthanbetween.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_lessthancongruence_smaller.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.
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

Lemma lemma_21helper :
	forall A B C E,
	TogetherGreater B A A E B E ->
	BetS A E C ->
	TT B A A C B E E C.
Proof.
	intros A B C E.
	intros TogetherGreater_B_A_A_E_B_E.
	intros BetS_A_E_C.

	destruct TogetherGreater_B_A_A_E_B_E as (H & BetS_B_A_H & Cong_A_H_A_E & Lt_B_E_B_H).
	pose proof (lemma_betweennotequal _ _ _ BetS_B_A_H) as (_ & neq_B_A & _).

	assert (~ eq B E) as n_eq_B_E.
	{
		intro eq_B_E.
		
		assert (Lt B B B H) as Lt_B_B_B_H by (setoid_rewrite eq_B_E at 2; exact Lt_B_E_B_H).

		destruct Lt_B_B_B_H as (K & BetS_B_K_H & Cong_B_K_B_B).

		assert (~ neq B K) as n_neq_B_K.
		{
			intro neq_B_K.
			epose proof (axiom_nocollapse _ _ _ _ neq_B_K Cong_B_K_B_B) as neq_B_B.
			assert (eq B B) as eq_B_B by (reflexivity).
			contradict eq_B_B.
			exact neq_B_B.
		}
		assert (eq_B_K := n_neq_B_K).
		apply Classical_Prop.NNPP in eq_B_K.

		
		assert (BetS B B H) as BetS_B_B_H by (setoid_rewrite eq_B_K at 2; exact BetS_B_K_H).

		pose proof (lemma_betweennotequal _ _ _ BetS_B_B_H) as (_ & neq_B_B & _).
		assert (eq B B) as eq_B_B by (reflexivity).
		contradict eq_B_B.
		exact neq_B_B.
	}
	assert (neq_B_E := n_eq_B_E).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_E_C) as (_ & _ & neq_A_C).
	pose proof (lemma_extension _ _ _ _ neq_B_A neq_A_C) as (F & BetS_B_A_F & Cong_A_F_A_C).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_E_C) as (neq_E_C & _ & _).
	pose proof (lemma_extension _ _ _ _ neq_B_E neq_E_C) as (G & BetS_B_E_G & Cong_E_G_E_C).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_A_F_A_C) as Cong_A_C_A_F.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_A_H_A_E) as Cong_A_E_A_H.
	pose proof (cn_congruencereflexive A E) as Cong_A_E_A_E.
	pose proof (lemma_s_lt _ _ _ _ _ BetS_A_E_C Cong_A_E_A_E) as Lt_A_E_A_C.
	pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_A_E_A_C Cong_A_C_A_F) as Lt_A_E_A_F.
	pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_A_E_A_F Cong_A_E_A_H) as Lt_A_H_A_F.
	pose proof (lemma_s_onray _ _ _ _ BetS_B_A_H BetS_B_A_F) as OnRay_A_H_F.
	pose proof (lemma_lessthanbetween _ _ _ Lt_A_H_A_F OnRay_A_H_F) as BetS_A_H_F.
	pose proof (lemma_differenceofparts _ _ _ _ _ _ Cong_A_E_A_H Cong_A_C_A_F BetS_A_E_C BetS_A_H_F) as Cong_E_C_H_F.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_E_G_E_C Cong_E_C_H_F) as Cong_E_G_H_F.
	pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_B_A_H BetS_A_H_F) as BetS_B_H_F.
	pose proof (lemma_lessthanadditive _ _ _ _ _ _ Lt_B_E_B_H BetS_B_E_G BetS_B_H_F Cong_E_G_H_F) as Lt_B_G_B_F.
	pose proof (lemma_s_TogetherGreater B A A C B G F BetS_B_A_F Cong_A_F_A_C Lt_B_G_B_F) as TogetherGreater_B_A_A_C_B_G.

	pose proof (lemma_s_TT B A A C B E E C G BetS_B_E_G Cong_E_G_E_C TogetherGreater_B_A_A_C_B_G) as TT_B_A_A_C_B_E_E_C.
	exact TT_B_A_A_C_B_E_E_C.
Qed.

End Euclid.
