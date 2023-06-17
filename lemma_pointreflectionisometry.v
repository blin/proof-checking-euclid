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
Require Import ProofCheckingEuclid.lemma_s_lt.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_onray.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
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

	pose proof (cn_congruencereflexive B C) as Cong_B_C_B_C.
	pose proof (cn_congruencereflexive B Q) as Cong_B_Q_B_Q.
	pose proof (cn_congruencereverse A C) as Cong_A_C_C_A.
	pose proof (cn_congruencereverse C B) as Cong_C_B_B_C.
	pose proof (cn_congruencereverse Q B) as Cong_Q_B_B_Q.

	destruct Midpoint_A_B_C as (BetS_A_B_C & Cong_A_B_B_C).
	destruct Midpoint_P_B_Q as (BetS_P_B_Q & Cong_P_B_B_Q).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_C) as BetS_C_B_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_C) as (neq_B_C & neq_A_B & neq_A_C).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_B_Q) as BetS_Q_B_P.
	pose proof (lemma_betweennotequal _ _ _ BetS_P_B_Q) as (neq_B_Q & neq_P_B & neq_P_Q).
	pose proof (lemma_betweennotequal _ _ _ BetS_Q_B_P) as (neq_B_P & neq_Q_B & neq_Q_P).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_A_B_B_C) as Cong_B_C_A_B.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_A_B_B_C) as (_ & _ & Cong_A_B_C_B).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_B_C_A_B) as (_ & _ & Cong_B_C_B_A).
	pose proof (lemma_doublereverse _ _ _ _ Cong_B_C_A_B) as (Cong_B_A_C_B & _).
	pose proof (lemma_doublereverse _ _ _ _ Cong_P_B_B_Q) as (Cong_Q_B_B_P & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_Q_B_B_P) as (_ & Cong_B_Q_B_P & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_P_B_B_Q) as Cong_B_Q_P_B.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_B_Q_B_P) as Cong_B_P_B_Q.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_B_C_B_A) as Cong_B_A_B_C.
	pose proof (lemma_doublereverse _ _ _ _ Cong_B_Q_P_B) as (Cong_B_P_Q_B & _).

	(* assert by cases *)
	assert (~ Col A B P \/ ~ ~ Col A B P) as [n_Col_A_B_P|Col_A_B_P] by (apply Classical_Prop.classic).
	{
		(* case n_Col_A_B_P *)
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_B_P) as nCol_A_B_P.

		pose proof (proposition_15a _ _ _ _ _ BetS_A_B_C BetS_P_B_Q nCol_A_B_P) as CongA_A_B_P_Q_B_C.

		pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_A_B_P_Q_B_C) as nCol_Q_B_C.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_Q_B_C) as CongA_Q_B_C_C_B_Q.

		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_B_P_Q_B_C CongA_Q_B_C_C_B_Q) as CongA_A_B_P_C_B_Q.
		pose proof (proposition_04 _ _ _ _ _ _ Cong_B_A_B_C Cong_B_P_B_Q CongA_A_B_P_C_B_Q) as (Cong_A_P_C_Q & _ & _).

		exact Cong_A_P_C_Q.
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
		pose proof (lemma_s_onray _ _ _ _ BetS_P_B_C BetS_P_B_Q) as OnRay_B_C_Q.
		pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_B_C_Q) as OnRay_B_Q_C.

		pose proof (lemma_s_lt _ _ _ _ _ BetS_B_A_P Cong_B_A_C_B) as Lt_C_B_B_P.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_C_B_B_P Cong_B_P_B_Q) as Lt_C_B_B_Q.
		pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_C_B_B_Q Cong_C_B_B_C) as Lt_B_C_B_Q.

		pose proof (proposition_03 _ _ _ _ _ _ Lt_B_C_B_Q Cong_B_Q_B_Q) as (H & BetS_B_H_Q & Cong_B_H_B_C).
		
		pose proof (lemma_s_onray_assert_bets_AEB B Q H BetS_B_H_Q neq_B_Q) as OnRay_B_Q_H.

		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_B_H_B_C) as Cong_B_C_B_H.

		pose proof (lemma_layoffunique _ _ _ _ OnRay_B_Q_C OnRay_B_Q_H Cong_B_C_B_H) as eq_C_H.
		assert (BetS B C Q) as BetS_B_C_Q by (rewrite eq_C_H; exact BetS_B_H_Q).

		pose proof (lemma_differenceofparts _ _ _ _ _ _ Cong_B_A_B_C Cong_B_P_B_Q BetS_B_A_P BetS_B_C_Q) as Cong_A_P_C_Q.

		exact Cong_A_P_C_Q.
	}
	{
		(* case BetS_A_B_P *)
		assert (BetS B P C \/ ~ BetS B P C) as [BetS_B_P_C|n_BetS_B_P_C] by (apply Classical_Prop.classic).
		{
			(* case BetS_B_P_C *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_P_C) as BetS_C_P_B.

			pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_C_P_B BetS_P_B_Q) as BetS_C_B_Q.
			pose proof (cn_sumofparts _ _ _ _ _ _ Cong_A_B_C_B Cong_B_P_B_Q BetS_A_B_P BetS_C_B_Q) as Cong_A_P_C_Q.

			exact Cong_A_P_C_Q.
		}
		(* case n_BetS_B_P_C *)
		assert (BetS B C P \/ ~ BetS B C P) as [BetS_B_C_P|n_BetS_B_C_P] by (apply Classical_Prop.classic).
		{
			(* case BetS_B_C_P *)
			pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_Q_B_P BetS_B_C_P) as BetS_Q_B_C.

			pose proof (axiom_betweennesssymmetry _ _ _ BetS_Q_B_C) as BetS_C_B_Q.
			pose proof (cn_sumofparts _ _ _ _ _ _ Cong_A_B_C_B Cong_B_P_B_Q BetS_A_B_P BetS_C_B_Q) as Cong_A_P_C_Q.

			exact Cong_A_P_C_Q.
		}
		(* case n_BetS_B_C_P *)

		pose proof (lemma_outerconnectivity _ _ _ _ BetS_A_B_P BetS_A_B_C n_BetS_B_P_C n_BetS_B_C_P) as eq_P_C.
		assert (Cong A B B P) as Cong_A_B_B_P by (rewrite eq_P_C; exact Cong_A_B_B_C).
		assert (BetS P B A) as BetS_P_B_A by (rewrite eq_P_C; exact BetS_C_B_A).
		assert (Cong A P C A) as Cong_A_P_C_A by (rewrite eq_P_C; exact Cong_A_C_C_A).

		pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_A_B_B_P Cong_B_P_B_Q) as Cong_A_B_B_Q.
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_A_B_B_Q) as Cong_B_Q_A_B.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_B_Q_A_B) as (_ & _ & Cong_B_Q_B_A).

		pose proof (lemma_extensionunique _ _ _ _ BetS_P_B_Q BetS_P_B_A Cong_B_Q_B_A) as eq_Q_A.
		assert (Cong A P C Q) as Cong_A_P_C_Q by (rewrite eq_Q_A; exact Cong_A_P_C_A).

		exact Cong_A_P_C_Q.
	}
	{
		(* case BetS_A_P_B *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_P_B) as BetS_B_P_A.
		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_P_B BetS_A_B_C) as BetS_P_B_C.
		pose proof (lemma_s_onray _ _ _ _ BetS_P_B_C BetS_P_B_Q) as OnRay_B_C_Q.

		pose proof (lemma_s_lt _ _ _ _ _ BetS_B_P_A Cong_B_P_Q_B) as Lt_Q_B_B_A.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_Q_B_B_A Cong_B_A_B_C) as Lt_Q_B_B_C.
		pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_Q_B_B_C Cong_Q_B_B_Q) as Lt_B_Q_B_C.

		pose proof (proposition_03 _ _ _ _ _ _ Lt_B_Q_B_C Cong_B_C_B_C) as (H & BetS_B_H_C & Cong_B_H_B_Q).
		
		pose proof (lemma_s_onray_assert_bets_AEB B C H BetS_B_H_C neq_B_C) as OnRay_B_C_H.

		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_B_H_B_Q) as Cong_B_Q_B_H.

		pose proof (lemma_layoffunique _ _ _ _ OnRay_B_C_Q OnRay_B_C_H Cong_B_Q_B_H) as eq_Q_H.
		assert (BetS B Q C) as BetS_B_Q_C by (rewrite eq_Q_H; exact BetS_B_H_C).

		pose proof (lemma_differenceofparts _ _ _ _ _ _ Cong_B_P_B_Q Cong_B_A_B_C BetS_B_P_A BetS_B_Q_C) as Cong_P_A_Q_C.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_P_A_Q_C) as (Cong_A_P_C_Q & _ & _).

		exact Cong_A_P_C_Q.
	}
Qed.

End Euclid.
