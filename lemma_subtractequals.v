Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_lessthantransitive.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_trichotomy_asymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_subtractequals :
	forall A B C D E,
	BetS A B C ->
	BetS A D E ->
	Cong B C D E ->
	BetS A C E ->
	BetS A B D.
Proof.
	intros A B C D E.
	intros BetS_A_B_C.
	intros BetS_A_D_E.
	intros Cong_BC_DE.
	intros BetS_A_C_E.

	pose proof (cn_congruencereflexive A B) as Cong_AB_AB.
	pose proof (cn_congruencereflexive B C) as Cong_BC_BC.
	pose proof (cn_congruencereflexive E B) as Cong_EB_EB.
	pose proof (cn_congruencereverse B E) as Cong_BE_EB.
	pose proof (cn_congruencereverse E D) as Cong_ED_DE.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BC_DE) as Cong_DE_BC.

	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_C) as (_ & neq_A_B & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_C_E) as (neq_C_E & _ & _).

	pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_A_B_C BetS_A_C_E) as BetS_A_B_E.
	pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_B_C BetS_A_C_E) as BetS_B_C_E.

	pose proof (lemma_s_onray_assert_bets_ABE _ _ _ BetS_A_B_C neq_A_B) as OnRay_AB_C.
	pose proof (lemma_s_onray_assert_bets_ABE _ _ _ BetS_A_B_E neq_A_B) as OnRay_AB_E.

	pose proof (by_def_Lt _ _ _ _ _ BetS_B_C_E Cong_BC_BC) as Lt_BC_BE.
	pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_BC_BE Cong_BE_EB) as Lt_BC_EB.


	assert (~ BetS A D B) as n_BetS_A_D_B.
	{
		intro BetS_A_D_B.

		pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_A_D_B BetS_A_B_C) as BetS_A_D_C.
		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_D_C BetS_A_C_E) as BetS_D_C_E.
		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_D_B BetS_A_B_C) as BetS_D_B_C.
		pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_D_B_C BetS_D_C_E) as BetS_D_B_E.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_B_E) as BetS_E_B_D.

		pose proof (by_def_Lt _ _ _ _ _ BetS_E_B_D Cong_EB_EB) as Lt_EB_ED.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_EB_ED Cong_ED_DE) as Lt_EB_DE.
		pose proof (lemma_lessthantransitive _ _ _ _ _ _ Lt_BC_EB Lt_EB_DE) as Lt_BC_DE.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_BC_DE Cong_DE_BC) as Lt_BC_BC.

		pose proof (lemma_trichotomy_asymmetric _ _ _ _ Lt_BC_BC) as n_Lt_BC_BC.

		contradict Lt_BC_BC.
		exact n_Lt_BC_BC.
	}

	assert (~ ~ BetS A B D) as n_n_BetS_A_B_D.
	{
		intro n_BetS_A_B_D.

		pose proof (axiom_connectivity _ _ _ _ BetS_A_B_E BetS_A_D_E n_BetS_A_B_D n_BetS_A_D_B) as eq_B_D.

		assert (Cong A B A D) as Cong_AB_AD by (rewrite <- eq_B_D; exact Cong_AB_AB).

		pose proof (cn_sumofparts _ _ _ _ _ _ Cong_AB_AD Cong_BC_DE BetS_A_B_C BetS_A_D_E) as Cong_AC_AE.

		pose proof (lemma_layoffunique _ _ _ _ OnRay_AB_C OnRay_AB_E Cong_AC_AE) as eq_C_E.

		contradict eq_C_E.
		exact neq_C_E.
	}
	assert (BetS_A_B_D := n_n_BetS_A_B_D).
	apply Classical_Prop.NNPP in BetS_A_B_D.

	exact BetS_A_B_D.
Qed.

End Euclid.
