Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_s_conga.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_ABCequalsCBA :
	forall A B C,
	nCol A B C ->
	CongA A B C C B A.
Proof.
	intros A B C.
	intros nCol_A_B_C.

	pose proof (
		lemma_NCdistinct _ _ _ nCol_A_B_C
	) as (neq_A_B & neq_B_C & _ & neq_B_A & neq_C_B & _).
	pose proof (lemma_extension _ _ _ _ neq_B_A neq_C_B) as (E & BetS_B_A_E & Cong_AE_CB).
	pose proof (lemma_extension _ _ _ _ neq_B_C neq_A_B) as (F & BetS_B_C_F & Cong_CF_AB).

	pose proof (lemma_doublereverse _ _ _ _ Cong_CF_AB) as (Cong_BA_FC & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_C_F) as BetS_F_C_B.
	pose proof (
		cn_sumofparts _ _ _ _ _ _ Cong_BA_FC Cong_AE_CB BetS_B_A_E BetS_F_C_B
	) as Cong_BE_FB.
	pose proof (cn_congruencereverse F B) as Cong_FB_BF.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_BE_FB Cong_FB_BF) as Cong_BE_BF.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BE_BF) as Cong_BF_BE.
	pose proof (cn_congruencereverse E F) as Cong_EF_FE.

	assert (BetS B E A \/ eq E A \/ BetS B A E) as BetS_B_E_A_or_eq_E_A_or_BetS_B_A_E.
	one_of_disjunct BetS_B_A_E.
	pose proof (lemma_onray_assert _ _ _ BetS_B_E_A_or_eq_E_A_or_BetS_B_A_E neq_B_A) as OnRay_BA_E.

	assert (BetS B F C \/ eq F C \/ BetS B C F) as BetS_B_F_C_or_eq_F_C_or_BetS_B_C_F.
	one_of_disjunct BetS_B_C_F.
	pose proof (lemma_onray_assert _ _ _ BetS_B_F_C_or_eq_F_C_or_BetS_B_C_F neq_B_C) as OnRay_BC_F.

	pose proof (
		lemma_s_conga
		_ _ _ _ _ _ _ _ _ _
		OnRay_BA_E
		OnRay_BC_F
		OnRay_BC_F
		OnRay_BA_E
		Cong_BE_BF
		Cong_BF_BE
		Cong_EF_FE
		nCol_A_B_C
	) as CongA_ABC_CBA.

	exact CongA_ABC_CBA.
Qed.

End Euclid.
