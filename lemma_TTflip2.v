Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_lessthancongruence_smaller.
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

	destruct TT_A_B_C_D_E_F_G_H as (J & BetS_E_F_J & Cong_FJ_GH & TogetherGreater_AB_CD_EJ).

	pose proof (lemma_betweennotequal _ _ _ BetS_E_F_J) as (neq_F_J & _ & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_F_J) as (_ & neq_E_F & _).

	pose proof (axiom_nocollapse _ _ _ _ neq_F_J Cong_FJ_GH) as neq_G_H.

	pose proof (lemma_inequalitysymmetric _ _ neq_G_H) as neq_H_G.
	pose proof (lemma_inequalitysymmetric _ _ neq_E_F) as neq_F_E.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_FJ_GH) as Cong_GH_FJ.

	destruct TogetherGreater_AB_CD_EJ as (K & BetS_A_B_K & Cong_BK_CD & Lt_EJ_AK).

	pose proof (lemma_extension _ _ _ _ neq_H_G neq_F_E) as (L & BetS_H_G_L & Cong_GL_FE).

	pose proof (cn_congruencereverse H L) as Cong_HL_LH.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_G_L) as BetS_L_G_H.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_GL_FE) as (Cong_LG_EF & _ & _).
	pose proof (cn_sumofparts L G H E F J Cong_LG_EF Cong_GH_FJ BetS_L_G_H BetS_E_F_J) as Cong_LH_EJ.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_HL_LH Cong_LH_EJ) as Cong_HL_EJ.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_HL_EJ) as Cong_EJ_HL.
	pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_EJ_AK Cong_EJ_HL) as Lt_HL_AK.

	pose proof (lemma_s_TogetherGreater _ _ _ _ _ _ _ BetS_A_B_K Cong_BK_CD Lt_HL_AK) as TogetherGreater_AB_CD_HL.

	pose proof (lemma_s_TT _ _ _ _ _ _ _ _ _ BetS_H_G_L Cong_GL_FE TogetherGreater_AB_CD_HL) as TT_A_B_C_D_H_G_F_E.

	exact TT_A_B_C_D_H_G_F_E.
Qed.

End Euclid.
