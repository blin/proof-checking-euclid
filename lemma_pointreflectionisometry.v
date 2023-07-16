Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.by_def_OnRay.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_differenceofparts.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_extensionunique.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_lessthancongruence_smaller.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_outerconnectivity.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.proposition_03.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_15a.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

(* Points A and P are reflected through point B. *)
Lemma lemma_pointreflectionisometry :
	forall A B C P Q,
	Midpoint A B C ->
	Midpoint P B Q ->
	neq A P ->
	Cong A P C Q.
Proof.
	intros A B C P Q.
	intros Midpoint_A_B_C.
	intros Midpoint_P_B_Q.
	intros neq_A_P.

	pose proof (cn_congruencereflexive B C) as Cong_BC_BC.
	pose proof (cn_congruencereflexive B Q) as Cong_BQ_BQ.
	pose proof (cn_congruencereverse A C) as Cong_AC_CA.
	pose proof (cn_congruencereverse C B) as Cong_CB_BC.
	pose proof (cn_congruencereverse Q B) as Cong_QB_BQ.

	destruct Midpoint_A_B_C as (BetS_A_B_C & Cong_AB_BC).
	destruct Midpoint_P_B_Q as (BetS_P_B_Q & Cong_PB_BQ).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_C) as BetS_C_B_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_C) as (neq_B_C & neq_A_B & neq_A_C).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_B_Q) as BetS_Q_B_P.
	pose proof (lemma_betweennotequal _ _ _ BetS_P_B_Q) as (neq_B_Q & neq_P_B & neq_P_Q).
	pose proof (lemma_betweennotequal _ _ _ BetS_Q_B_P) as (neq_B_P & neq_Q_B & neq_Q_P).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AB_BC) as Cong_BC_AB.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AB_BC) as (_ & _ & Cong_AB_CB).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_BC_AB) as (_ & _ & Cong_BC_BA).
	pose proof (lemma_doublereverse _ _ _ _ Cong_BC_AB) as (Cong_BA_CB & _).
	pose proof (lemma_doublereverse _ _ _ _ Cong_PB_BQ) as (Cong_QB_BP & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_QB_BP) as (_ & Cong_BQ_BP & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_PB_BQ) as Cong_BQ_PB.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BQ_BP) as Cong_BP_BQ.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BC_BA) as Cong_BA_BC.
	pose proof (lemma_doublereverse _ _ _ _ Cong_BQ_PB) as (Cong_BP_QB & _).

	(* assert by cases *)
	assert (~ Col A B P \/ ~ ~ Col A B P) as [n_Col_A_B_P|Col_A_B_P] by (apply Classical_Prop.classic).
	{
		(* case n_Col_A_B_P *)
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_B_P) as nCol_A_B_P.

		pose proof (proposition_15a _ _ _ _ _ BetS_A_B_C BetS_P_B_Q nCol_A_B_P) as CongA_ABP_QBC.

		pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_ABP_QBC) as nCol_Q_B_C.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_Q_B_C) as CongA_QBC_CBQ.

		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_ABP_QBC CongA_QBC_CBQ) as CongA_ABP_CBQ.
		pose proof (proposition_04 _ _ _ _ _ _ Cong_BA_BC Cong_BP_BQ CongA_ABP_CBQ) as (Cong_AP_CQ & _ & _).

		exact Cong_AP_CQ.
	}
	(* case Col_A_B_P *)
	apply Classical_Prop.NNPP in Col_A_B_P.

	(* assert by cases *)
	destruct Col_A_B_P as [eq_A_B | [eq_A_P | [eq_B_P | [BetS_B_A_P | [BetS_A_B_P | BetS_A_P_B]]]]].
	{
		(* case eq_A_B *)

		contradict eq_A_B.
		exact neq_A_B.
	}
	{
		(* case eq_A_P *)
		contradict eq_A_P.
		exact neq_A_P.
	}
	{
		(* case eq_B_P *)

		contradict eq_B_P.
		exact neq_B_P.
	}
	{
		(* case BetS_B_A_P *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_P) as BetS_P_A_B.

		pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_P_A_B BetS_A_B_C) as BetS_P_B_C.
		pose proof (by_def_OnRay _ _ _ _ BetS_P_B_C BetS_P_B_Q) as OnRay_BC_Q.
		pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_BC_Q) as OnRay_BQ_C.

		pose proof (by_def_Lt _ _ _ _ _ BetS_B_A_P Cong_BA_CB) as Lt_CB_BP.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_CB_BP Cong_BP_BQ) as Lt_CB_BQ.
		pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_CB_BQ Cong_CB_BC) as Lt_BC_BQ.

		pose proof (proposition_03 _ _ _ _ _ _ Lt_BC_BQ Cong_BQ_BQ) as (H & BetS_B_H_Q & Cong_BH_BC).

		pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_B_H_Q neq_B_Q) as OnRay_BQ_H.

		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BH_BC) as Cong_BC_BH.

		pose proof (lemma_layoffunique _ _ _ _ OnRay_BQ_C OnRay_BQ_H Cong_BC_BH) as eq_C_H.
		assert (BetS B C Q) as BetS_B_C_Q by (rewrite eq_C_H; exact BetS_B_H_Q).

		pose proof (lemma_differenceofparts _ _ _ _ _ _ Cong_BA_BC Cong_BP_BQ BetS_B_A_P BetS_B_C_Q) as Cong_AP_CQ.

		exact Cong_AP_CQ.
	}
	{
		(* case BetS_A_B_P *)
		assert (BetS B P C \/ ~ BetS B P C) as [BetS_B_P_C|n_BetS_B_P_C] by (apply Classical_Prop.classic).
		{
			(* case BetS_B_P_C *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_P_C) as BetS_C_P_B.

			pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_C_P_B BetS_P_B_Q) as BetS_C_B_Q.
			pose proof (cn_sumofparts _ _ _ _ _ _ Cong_AB_CB Cong_BP_BQ BetS_A_B_P BetS_C_B_Q) as Cong_AP_CQ.

			exact Cong_AP_CQ.
		}
		(* case n_BetS_B_P_C *)
		assert (BetS B C P \/ ~ BetS B C P) as [BetS_B_C_P|n_BetS_B_C_P] by (apply Classical_Prop.classic).
		{
			(* case BetS_B_C_P *)
			pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_Q_B_P BetS_B_C_P) as BetS_Q_B_C.

			pose proof (axiom_betweennesssymmetry _ _ _ BetS_Q_B_C) as BetS_C_B_Q.
			pose proof (cn_sumofparts _ _ _ _ _ _ Cong_AB_CB Cong_BP_BQ BetS_A_B_P BetS_C_B_Q) as Cong_AP_CQ.

			exact Cong_AP_CQ.
		}
		(* case n_BetS_B_C_P *)

		pose proof (lemma_outerconnectivity _ _ _ _ BetS_A_B_P BetS_A_B_C n_BetS_B_P_C n_BetS_B_C_P) as eq_P_C.
		assert (Cong A B B P) as Cong_AB_BP by (rewrite eq_P_C; exact Cong_AB_BC).
		assert (BetS P B A) as BetS_P_B_A by (rewrite eq_P_C; exact BetS_C_B_A).
		assert (Cong A P C A) as Cong_AP_CA by (rewrite eq_P_C; exact Cong_AC_CA).

		pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_AB_BP Cong_BP_BQ) as Cong_AB_BQ.
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AB_BQ) as Cong_BQ_AB.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_BQ_AB) as (_ & _ & Cong_BQ_BA).

		pose proof (lemma_extensionunique _ _ _ _ BetS_P_B_Q BetS_P_B_A Cong_BQ_BA) as eq_Q_A.
		assert (Cong A P C Q) as Cong_AP_CQ by (rewrite eq_Q_A; exact Cong_AP_CA).

		exact Cong_AP_CQ.
	}
	{
		(* case BetS_A_P_B *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_P_B) as BetS_B_P_A.
		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_P_B BetS_A_B_C) as BetS_P_B_C.
		pose proof (by_def_OnRay _ _ _ _ BetS_P_B_C BetS_P_B_Q) as OnRay_BC_Q.

		pose proof (by_def_Lt _ _ _ _ _ BetS_B_P_A Cong_BP_QB) as Lt_QB_BA.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_QB_BA Cong_BA_BC) as Lt_QB_BC.
		pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_QB_BC Cong_QB_BQ) as Lt_BQ_BC.

		pose proof (proposition_03 _ _ _ _ _ _ Lt_BQ_BC Cong_BC_BC) as (H & BetS_B_H_C & Cong_BH_BQ).

		pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_B_H_C neq_B_C) as OnRay_BC_H.

		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BH_BQ) as Cong_BQ_BH.

		pose proof (lemma_layoffunique _ _ _ _ OnRay_BC_Q OnRay_BC_H Cong_BQ_BH) as eq_Q_H.
		assert (BetS B Q C) as BetS_B_Q_C by (rewrite eq_Q_H; exact BetS_B_H_C).

		pose proof (lemma_differenceofparts _ _ _ _ _ _ Cong_BP_BQ Cong_BA_BC BetS_B_P_A BetS_B_Q_C) as Cong_PA_QC.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_PA_QC) as (Cong_AP_CQ & _ & _).

		exact Cong_AP_CQ.
	}
Qed.

End Euclid.
