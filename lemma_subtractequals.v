Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_lessthantransitive.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_s_lt.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
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
	intros Cong_B_C_D_E.
	intros BetS_A_C_E.


	assert (~ BetS A D B) as n_BetS_A_D_B.
	{
		intro BetS_A_D_B.
		pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_A_D_B BetS_A_B_C) as BetS_A_D_C.
		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_B_C BetS_A_C_E) as BetS_B_C_E.
		pose proof (cn_congruencereflexive B C) as Cong_B_C_B_C.
		pose proof (lemma_s_lt _ _ _ _ _ BetS_B_C_E Cong_B_C_B_C) as Lt_B_C_B_E.
		pose proof (cn_congruencereverse B E) as Cong_B_E_E_B.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_B_C_B_E Cong_B_E_E_B) as Lt_B_C_E_B.
		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_D_C BetS_A_C_E) as BetS_D_C_E.
		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_D_B BetS_A_B_C) as BetS_D_B_C.
		pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_D_B_C BetS_D_C_E) as BetS_D_B_E.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_B_E) as BetS_E_B_D.
		pose proof (cn_congruencereflexive E B) as Cong_E_B_E_B.
		pose proof (lemma_s_lt _ _ _ _ _ BetS_E_B_D Cong_E_B_E_B) as Lt_E_B_E_D.
		pose proof (cn_congruencereverse E D) as Cong_E_D_D_E.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_E_B_E_D Cong_E_D_D_E) as Lt_E_B_D_E.
		pose proof (lemma_lessthantransitive _ _ _ _ _ _ Lt_B_C_E_B Lt_E_B_D_E) as Lt_B_C_D_E.
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_B_C_D_E) as Cong_D_E_B_C.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_B_C_D_E Cong_D_E_B_C) as Lt_B_C_B_C.
		pose proof (lemma_trichotomy_asymmetric _ _ _ _ Lt_B_C_B_C) as n_Lt_B_C_B_C.

		contradict Lt_B_C_B_C.
		exact n_Lt_B_C_B_C.
	}

	assert (~ ~ BetS A B D) as n_n_BetS_A_B_D.
	{
		intro n_BetS_A_B_D.

		pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_A_B_C BetS_A_C_E) as BetS_A_B_E.
		pose proof (axiom_connectivity _ _ _ _ BetS_A_B_E BetS_A_D_E n_BetS_A_B_D n_BetS_A_D_B) as eq_B_D.
		pose proof (cn_congruencereflexive A B) as Cong_A_B_A_B.
		
		assert (Cong A B A D) as Cong_A_B_A_D by (rewrite <- eq_B_D; exact Cong_A_B_A_B).

		pose proof (cn_sumofparts _ _ _ _ _ _ Cong_A_B_A_D Cong_B_C_D_E BetS_A_B_C BetS_A_D_E) as Cong_A_C_A_E.
		
		pose proof (lemma_betweennotequal _ _ _ BetS_A_B_C) as (_ & neq_A_B & _).
		pose proof (lemma_s_onray_assert_bets_ABE A B E BetS_A_B_E neq_A_B) as OnRay_A_B_E.
		pose proof (lemma_s_onray_assert_bets_ABE A B C BetS_A_B_C neq_A_B) as OnRay_A_B_C.
		pose proof (lemma_layoffunique _ _ _ _ OnRay_A_B_C OnRay_A_B_E Cong_A_C_A_E) as eq_C_E.
		pose proof (lemma_betweennotequal _ _ _ BetS_A_C_E) as (neq_C_E & _ & _).

		contradict eq_C_E.
		exact neq_C_E.
	}
	assert (BetS_A_B_D := n_n_BetS_A_B_D).
	apply Classical_Prop.NNPP in BetS_A_B_D.

	exact BetS_A_B_D.
Qed.

End Euclid.
