Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_differenceofparts.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_extensionunique.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABD_BCD_ACD.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_outerconnectivity :
	forall A B C D,
	BetS A B C ->
	BetS A B D ->
	~ BetS B C D ->
	~ BetS B D C ->
	eq C D.
Proof.
	intros A B C D.
	intros BetS_A_B_C.
	intros BetS_A_B_D.
	intros nBetS_B_C_D.
	intros nBetS_B_D_C.

	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_C) as (_ & _ & neq_A_C).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_D) as (_ & _ & neq_A_D).
	pose proof (lemma_extension _ _ _ _ neq_A_C neq_A_D) as (E & BetS_A_C_E & Cong_CE_AD).
	pose proof (lemma_extension _ _ _ _ neq_A_D neq_A_C) as (F & BetS_A_D_F & Cong_DF_AC).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_F) as BetS_F_D_A.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_D) as BetS_D_B_A.
	pose proof (lemma_orderofpoints_ABD_BCD_ACD _ _ _ _ BetS_F_D_A BetS_D_B_A) as BetS_F_B_A.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_B_A) as BetS_A_B_F.
	pose proof (cn_congruencereverse F D) as Cong_FD_DF.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_FD_DF Cong_DF_AC) as Cong_FD_AC.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_CE_AD) as Cong_AD_CE.
	pose proof (cn_congruencereverse D A) as Cong_DA_AD.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_DA_AD Cong_AD_CE) as Cong_DA_CE.
	pose proof (
		cn_sumofparts _ _ _ _ _ _ Cong_FD_AC Cong_DA_CE BetS_F_D_A BetS_A_C_E
	) as Cong_FA_AE.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_FA_AE) as (_ & Cong_AF_AE & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AF_AE) as Cong_AE_AF.

	pose proof (cn_congruencereflexive A B) as Cong_AB_AB.
	pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_A_B_C BetS_A_C_E) as BetS_A_B_E.
	pose proof (
		lemma_differenceofparts _ _ _ _ _ _ Cong_AB_AB Cong_AE_AF BetS_A_B_E BetS_A_B_F
	) as Cong_BE_BF.
	pose proof (lemma_extensionunique _ _ _ _ BetS_A_B_E BetS_A_B_F Cong_BE_BF) as eq_E_F.

	assert (BetS A D E) as BetS_A_D_E by (rewrite eq_E_F; exact BetS_A_D_F).

	pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_B_C BetS_A_C_E) as BetS_B_C_E.
	pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_B_D BetS_A_D_E) as BetS_B_D_E.
	pose proof (axiom_connectivity _ _ _ _ BetS_B_C_E BetS_B_D_E nBetS_B_C_D nBetS_B_D_C) as eq_C_D.
	exact eq_C_D.
Qed.

End Euclid.


