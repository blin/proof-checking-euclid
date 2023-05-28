Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
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
Require Import ProofCheckingEuclid.lemma_s_TT.
Require Import ProofCheckingEuclid.lemma_s_TogetherGreater.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_lt.
Require Import ProofCheckingEuclid.lemma_s_onray.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_21helper :
	forall A B C E,
	TogetherGreater B A A E B E ->
	BetS A E C ->
	TT B A A C B E E C.
Proof.
	intros A B C E.
	intros TogetherGreater_BA_AE_BE.
	intros BetS_A_E_C.

	assert (eq B B) as eq_B_B by (reflexivity).

	pose proof (cn_congruencereflexive A E) as Cong_AE_AE.

	destruct TogetherGreater_BA_AE_BE as (H & BetS_B_A_H & Cong_AH_AE & Lt_BE_BH).
	pose proof (lemma_betweennotequal _ _ _ BetS_B_A_H) as (_ & neq_B_A & _).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_E_C) as (neq_E_C  & _ & neq_A_C).

	assert (~ eq B E) as n_eq_B_E.
	{
		intro eq_B_E.

		assert (Lt B B B H) as Lt_BB_BH by (setoid_rewrite eq_B_E at 2; exact Lt_BE_BH).

		destruct Lt_BB_BH as (K & BetS_B_K_H & Cong_BK_BB).

		assert (~ neq B K) as n_neq_B_K.
		{
			intro neq_B_K.
			pose proof (axiom_nocollapse _ _ _ _ neq_B_K Cong_BK_BB) as neq_B_B.
			contradict eq_B_B.
			exact neq_B_B.
		}
		assert (eq_B_K := n_neq_B_K).
		apply Classical_Prop.NNPP in eq_B_K.

		assert (BetS B B H) as BetS_B_B_H by (setoid_rewrite eq_B_K at 2; exact BetS_B_K_H).

		pose proof (lemma_betweennotequal _ _ _ BetS_B_B_H) as (_ & neq_B_B & _).

		contradict eq_B_B.
		exact neq_B_B.
	}
	assert (neq_B_E := n_eq_B_E).

	pose proof (lemma_extension _ _ _ _ neq_B_A neq_A_C) as (F & BetS_B_A_F & Cong_AF_AC).
	pose proof (lemma_extension _ _ _ _ neq_B_E neq_E_C) as (G & BetS_B_E_G & Cong_EG_EC).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AF_AC) as Cong_AC_AF.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AH_AE) as Cong_AE_AH.

	pose proof (lemma_s_onray _ _ _ _ BetS_B_A_H BetS_B_A_F) as OnRay_AH_F.
	pose proof (lemma_s_lt _ _ _ _ _ BetS_A_E_C Cong_AE_AE) as Lt_AE_AC.
	pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_AE_AC Cong_AC_AF) as Lt_AE_AF.
	pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_AE_AF Cong_AE_AH) as Lt_AH_AF.
	pose proof (lemma_lessthanbetween _ _ _ Lt_AH_AF OnRay_AH_F) as BetS_A_H_F.
	pose proof (lemma_differenceofparts _ _ _ _ _ _ Cong_AE_AH Cong_AC_AF BetS_A_E_C BetS_A_H_F) as Cong_EC_HF.

	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_EG_EC Cong_EC_HF) as Cong_EG_HF.
	pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_B_A_H BetS_A_H_F) as BetS_B_H_F.
	pose proof (lemma_lessthanadditive _ _ _ _ _ _ Lt_BE_BH BetS_B_E_G BetS_B_H_F Cong_EG_HF) as Lt_BG_BF.

	pose proof (lemma_s_TogetherGreater _ _ _ _ _ _ _ BetS_B_A_F Cong_AF_AC Lt_BG_BF) as TogetherGreater_BA_AC_BG.

	pose proof (lemma_s_TT _ _ _ _ _ _ _ _ _ BetS_B_E_G Cong_EG_EC TogetherGreater_BA_AC_BG) as TT_B_A_A_C_B_E_E_C.

	exact TT_B_A_A_C_B_E_E_C.
Qed.

End Euclid.
