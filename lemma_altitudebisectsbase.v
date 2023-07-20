Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_def_Midpoint.
Require Import ProofCheckingEuclid.by_def_OnRay.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_RightTriangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Cong_doublereverse.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_leg_change.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extensionunique.
Require Import ProofCheckingEuclid.proposition_04.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

(*
	lemma_altitudebisectsbase_isosceles would be a more appropriate name,
	but the change in clarity is fairly minor, so I'm leaving it as is.
*)
Lemma lemma_altitudebisectsbase :
	forall A B M P,
	BetS A M B ->
	Cong A P B P ->
	RightTriangle A M P ->
	Midpoint A M B.
Proof.
	intros A B M P.
	intros BetS_A_M_B.
	intros Cong_AP_BP.
	intros RightTriangle_AMP.

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AP_BP) as (Cong_PA_PB & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_PA_PB) as (_ & Cong_AP_PB & _ ).

	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_AMP) as nCol_A_M_P.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_M_P) as (_ & _ & neq_A_P & _ & _ & neq_P_A).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_M_P) as (_ & _ & _ & nCol_A_P_M & _).

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_P_A) as OnRay_PA_A.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_AMP) as RightTriangle_PMA.
	destruct RightTriangle_AMP as (C & BetS_A_M_C & Cong_AM_CM & Cong_AP_CP & neq_M_P).
	destruct RightTriangle_PMA as (Q & BetS_P_M_Q & Cong_PM_QM & Cong_PA_QA & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_M_C) as BetS_C_M_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_P_M_Q) as (_ & neq_P_M & _).
	pose proof (by_def_OnRay _ _ _ _ BetS_A_M_C BetS_A_M_B) as OnRay_MC_B.
	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_P_M_Q neq_P_M) as OnRay_PM_Q.

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AM_CM) as Cong_CM_AM.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_PM_QM) as Cong_QM_PM.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_QM_PM) as (_ & Cong_MQ_PM & _ ).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_MQ_PM) as Cong_PM_MQ.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AP_CP) as Cong_CP_AP.
	pose proof (by_prop_Cong_doublereverse _ _ _ _ Cong_PA_QA) as (Cong_AQ_AP & _).

	pose proof (by_def_RightTriangle _ _ _ _ BetS_C_M_A Cong_CM_AM Cong_CP_AP neq_M_P) as RightTriangle_CMP.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_CMP) as RightTriangle_PMC.
	pose proof (by_prop_RightTriangle_leg_change _ _ _ _ RightTriangle_PMC OnRay_MC_B) as RightTriangle_PMB.

	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_PMB) as nCol_P_M_B.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_P_M_B) as (_ & _ & neq_P_B & _ & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_P_B) as OnRay_PB_B.

	destruct RightTriangle_PMB as (E & BetS_P_M_E & Cong_PM_EM & Cong_PB_EB & _).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_PM_EM) as Cong_EM_PM.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_EM_PM Cong_PM_MQ) as Cong_EM_MQ.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_EM_MQ) as (_ & Cong_ME_MQ & _ ).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_ME_MQ) as Cong_MQ_ME.

	pose proof (lemma_extensionunique _ _ _ _ BetS_P_M_Q BetS_P_M_E Cong_MQ_ME) as eq_Q_E.
	assert (Cong P B Q B) as Cong_PB_QB by (rewrite eq_Q_E; exact Cong_PB_EB).
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AP_PB Cong_PB_QB) as Cong_AP_QB.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AQ_AP Cong_AP_QB) as Cong_AQ_QB.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AQ_QB) as (_ & _ & Cong_AQ_BQ).

	pose proof (cn_congruencereflexive P Q) as Cong_PQ_PQ.
	pose proof (cn_congruencereflexive P M) as Cong_PM_PM.

	pose proof (
		by_def_CongA
		_ _ _ _ _ _
		_ _ _ _
		OnRay_PA_A
		OnRay_PM_Q
		OnRay_PB_B
		OnRay_PM_Q
		Cong_PA_PB
		Cong_PQ_PQ
		Cong_AQ_BQ
		nCol_A_P_M
	) as CongA_APM_BPM.

	pose proof (
		proposition_04
		_ _ _ _ _ _
		Cong_PA_PB
		Cong_PM_PM
		CongA_APM_BPM
	) as (Cong_AM_BM & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AM_BM) as (_ & _ & Cong_AM_MB).

	pose proof (by_def_Midpoint _ _ _ BetS_A_M_B Cong_AM_MB) as Midpoint_A_M_B.

	exact Midpoint_A_M_B.
Qed.

End Euclid.
