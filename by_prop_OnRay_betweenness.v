Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence.
Require Import ProofCheckingEuclid.by_prop_OnRay_neq_A_B.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_extensionunique.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.


Lemma by_prop_OnRay_betweenness :
	forall A B P,
	OnRay A B P ->
	neq P B ->
	~ BetS A P B ->
	BetS A B P.
Proof.
	intros A B P.
	intros OnRay_AB_P.
	intros neq_P_B.
	intros nBetS_A_P_B.

	pose proof (by_prop_OnRay_neq_A_B _ _ _ OnRay_AB_P) as neq_A_B.
	destruct OnRay_AB_P as (E & BetS_E_A_P & BetS_E_A_B).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_A_P) as (neq_A_P & _).
	pose proof (lemma_extension _ _ _ _ neq_A_B neq_A_P) as (D & BetS_A_B_D & Cong_BD_AP).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_D) as BetS_D_B_A.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BD_AP) as (_ & Cong_DB_AP & _).
	pose proof (by_def_Lt _ _ _ _ _ BetS_D_B_A Cong_DB_AP) as Lt_AP_DA.

	pose proof (cn_congruencereverse D A) as Cong_DA_AD.
	pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_AP_DA Cong_DA_AD) as Lt_AP_AD.

	destruct Lt_AP_AD as (F & BetS_A_F_D & Cong_AF_AP).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AF_AP) as Cong_AP_AF.
	pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_E_A_B BetS_A_B_D) as BetS_E_A_D.
	pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_E_A_D BetS_A_F_D) as BetS_E_A_F.

	pose proof (lemma_extensionunique _ _ _ _ BetS_E_A_P BetS_E_A_F Cong_AP_AF) as eq_P_F.

	assert (BetS A P D) as BetS_A_P_D by (rewrite eq_P_F;  exact BetS_A_F_D).

	assert (~ ~ BetS A B P) as BetS_A_B_P.
	{
		intro nBetS_A_B_P.

		pose proof (
			axiom_connectivity _ _ _ _ BetS_A_B_D BetS_A_P_D nBetS_A_B_P nBetS_A_P_B
		) as eq_B_P.
		pose proof (by_prop_neq_symmetric _ _ neq_P_B) as neq_B_P.

		contradict eq_B_P.
		exact neq_B_P.
	}
	apply Classical_Prop.NNPP in BetS_A_B_P.
	exact BetS_A_B_P.
Qed.

End Euclid.
