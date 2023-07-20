Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence_smaller.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_outerconnectivity.
Require Import ProofCheckingEuclid.lemma_trichotomy_asymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_Lt_additive :
	forall A B C D E F,
	Lt A B C D ->
	BetS A B E ->
	BetS C D F ->
	Cong B E D F ->
	Lt A E C F.
Proof.
	intros A B C D E F.
	intros Lt_AB_CD.
	intros BetS_A_B_E.
	intros BetS_C_D_F.
	intros Cong_BE_DF.

	destruct Lt_AB_CD as (b & BetS_C_b_D & Cong_Cb_AB).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_b_D) as (_ & neq_C_b & _).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_Cb_AB) as Cong_AB_Cb.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_B_E) as (neq_B_E & _ & _).

	pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_C_b_D BetS_C_D_F) as BetS_C_b_F.
	pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_C_b_D BetS_C_D_F) as BetS_b_D_F.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_b_F) as (neq_b_F & _ & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_b_D_F) as BetS_F_D_b.

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BE_DF) as Cong_DF_BE.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_DF_BE) as (_ & Cong_FD_BE & _).

	pose proof (lemma_extension _ _ _ _ neq_C_b neq_B_E) as (e & BetS_C_b_e & Cong_be_BE).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_be_BE) as Cong_BE_be.
	pose proof (cn_sumofparts A _ E C _ e Cong_AB_Cb Cong_BE_be BetS_A_B_E BetS_C_b_e) as Cong_AE_Ce.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AE_Ce) as Cong_Ce_AE.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_be_BE Cong_BE_DF) as Cong_be_DF.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_be_DF) as Cong_DF_be.

	pose proof (cn_congruencereflexive F D) as Cong_FD_FD.
	pose proof (cn_congruencereflexive b F) as Cong_bF_bF.
	pose proof (cn_congruencereflexive e D) as Cong_eD_eD.
	pose proof (cn_congruencereverse F D) as Cong_FD_DF.
	pose proof (cn_congruencereverse F b) as Cong_Fb_bF.

	pose proof (by_def_Lt _ _ _ _ _ BetS_F_D_b Cong_FD_FD) as Lt_FD_Fb.
	pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_FD_Fb Cong_Fb_bF) as Lt_FD_bF.
	pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_FD_bF Cong_FD_BE) as Lt_BE_bF.
	pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_FD_bF Cong_FD_DF) as Lt_DF_bF.
	pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_DF_bF Cong_DF_be) as Lt_be_bF.


	assert (~ BetS b F e) as n_BetS_b_F_e.
	{
		intro BetS_b_F_e.

		destruct Lt_be_bF as (q & BetS_b_q_F & Cong_bq_be).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_b_q_F) as (_ & neq_b_q & _).
		pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_b_q_F neq_b_F) as OnRay_bF_q.
		pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_b_F_e neq_b_F) as OnRay_bF_e.
		pose proof (lemma_layoffunique _ _ _ _ OnRay_bF_q OnRay_bF_e Cong_bq_be) as eq_q_e.

		assert (BetS b e F) as BetS_b_e_F by (rewrite <- eq_q_e; exact BetS_b_q_F).

		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_b_F_e BetS_b_e_F) as BetS_F_e_F.

		pose proof (axiom_betweennessidentity F e) as n_BetS_F_e_F.

		contradict BetS_F_e_F.
		exact n_BetS_F_e_F.
	}

	assert (~ eq F e) as n_eq_F_e.
	{
		intro eq_F_e.

		assert (Cong b F B E) as Cong_bF_BE by (rewrite eq_F_e; exact Cong_be_BE).

		pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_bF_BE Cong_BE_be) as Cong_bF_be.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_BE_bF Cong_bF_be) as Lt_BE_be.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_BE_bF Cong_bF_BE) as Lt_BE_BE.

		pose proof (lemma_trichotomy_asymmetric _ _ _ _ Lt_BE_BE) as n_Lt_BE_BE.

		contradict Lt_BE_BE.
		exact n_Lt_BE_BE.
	}

	assert (~ ~ BetS b e F) as n_n_BetS_b_e_F.
	{
		intro n_BetS_b_e_F.

		pose proof (lemma_outerconnectivity _ _ _ _ BetS_C_b_F BetS_C_b_e n_BetS_b_F_e n_BetS_b_e_F) as eq_F_e.

		contradict eq_F_e.
		exact n_eq_F_e.
	}
	assert (BetS_b_e_F := n_n_BetS_b_e_F).
	apply Classical_Prop.NNPP in BetS_b_e_F.

	pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_C_b_e BetS_b_e_F) as BetS_C_e_F.

	pose proof (by_def_Lt _ _ _ _ _ BetS_C_e_F Cong_Ce_AE) as Lt_AE_CF.

	exact Lt_AE_CF.
Qed.

End Euclid.
