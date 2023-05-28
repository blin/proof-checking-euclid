Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_lessthancongruence_smaller.
Require Import ProofCheckingEuclid.lemma_lessthannotequal.
Require Import ProofCheckingEuclid.lemma_ondiameter.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_outcirc_beyond_perimeter.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_subtractequals.
Require Import ProofCheckingEuclid.lemma_together.
Require Import ProofCheckingEuclid.lemma_trichotomy_asymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_22 :
	forall A B C E F a b c,
	TogetherGreater A a B b C c ->
	TogetherGreater A a C c B b ->
	TogetherGreater B b C c A a ->
	neq F E ->
	exists X Y, Cong F X B b /\ Cong F Y A a /\ Cong X Y C c /\ OnRay F E X /\ Triangle F X Y.
Proof.
	intros A B C E F a b c.
	intros TogetherGreater_Aa_Bb_Cc.
	intros TogetherGreater_Aa_Cc_Bb.
	intros TogetherGreater_Bb_Cc_Aa.
	intros neq_F_E.

	assert (TogetherGreater_Aa_Bb_Cc2 := TogetherGreater_Aa_Bb_Cc).
	destruct TogetherGreater_Aa_Bb_Cc2 as (P & BetS_A_a_P & Cong_aP_Bb & Lt_Cc_AP).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_a_P) as (neq_a_P  & neq_A_a & _).
	pose proof (axiom_nocollapse _ _ _ _ neq_a_P Cong_aP_Bb) as neq_B_b.
	pose proof (lemma_lessthannotequal _ _ _ _ Lt_Cc_AP) as (neq_C_c & _).

	pose proof (lemma_layoff _ _ _ _ neq_F_E neq_B_b) as (G & OnRay_FE_G & Cong_FG_Bb).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_FG_Bb) as Cong_Bb_FG.
	pose proof (axiom_nocollapse _ _ _ _ neq_B_b Cong_Bb_FG) as neq_F_G.
	pose proof (lemma_inequalitysymmetric _ _ neq_F_G) as neq_G_F.

	pose proof (lemma_extension _ _ _ _ neq_F_G neq_C_c) as (H & BetS_F_G_H & Cong_GH_Cc).
	pose proof (lemma_extension _ _ _ _ neq_G_F neq_A_a) as (D & BetS_G_F_D & Cong_FD_Aa).

	pose proof (lemma_congruenceflip _ _ _ _ Cong_FD_Aa) as (_ & Cong_DF_Aa & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_F_D) as BetS_D_F_G.
	pose proof (lemma_betweennotequal _ _ _ BetS_G_F_D) as (neq_F_D & _ & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_F_G_H) as (neq_G_H & _ & _).

	pose proof (cn_congruencereflexive C c) as Cong_Cc_Cc.
	pose proof (cn_congruencereflexive F D) as Cong_FD_FD.
	pose proof (cn_congruencereflexive G H) as Cong_GH_GH.
	pose proof (cn_congruencereverse D G) as Cong_DG_GD.

	pose proof (lemma_together _ _ _ _ _ _ _ _ _ _ _ TogetherGreater_Bb_Cc_Aa Cong_FG_Bb Cong_GH_Cc BetS_F_G_H Cong_DF_Aa) as (Lt_DF_FH & _).
	destruct Lt_DF_FH as (M & BetS_F_M_H & Cong_FM_DF).

	pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_D_F_G BetS_F_G_H) as BetS_D_F_H.
	pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_D_F_H BetS_F_M_H) as BetS_D_F_M.
	pose proof (lemma_betweennotequal _ _ _ BetS_F_M_H) as (_ & neq_F_M & _).

	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_FM_DF Cong_DF_Aa) as Cong_FM_Aa.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_FM_Aa) as Cong_Aa_FM.

	pose proof (lemma_extension _ _ _ _ neq_F_M neq_C_c) as (J & BetS_F_M_J & Cong_MJ_Cc).

	pose proof (lemma_together _ _ _ _ _ _ _ _ _ _ _ TogetherGreater_Aa_Cc_Bb Cong_FM_Aa Cong_MJ_Cc BetS_F_M_J Cong_FG_Bb) as (Lt_FG_FJ & _).
	pose proof (lemma_together _ _ _ _ _ _ _ _ _ _ _ TogetherGreater_Aa_Bb_Cc Cong_DF_Aa Cong_FG_Bb BetS_D_F_G Cong_Cc_Cc) as (Lt_Cc_DG & _).

	pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_Cc_DG Cong_DG_GD) as Lt_Cc_GD.

	destruct Lt_Cc_GD as (N & BetS_G_N_D & Cong_GN_Cc).
	destruct Lt_FG_FJ as (Q & BetS_F_Q_J & Cong_FQ_FG).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_FD_Aa) as Cong_Aa_FD.
	pose proof (cn_congruencetransitive _ _ _ _ _ _ Cong_Aa_FM Cong_Aa_FD) as Cong_FM_FD.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_MJ_Cc) as Cong_Cc_MJ.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_GN_Cc Cong_Cc_MJ) as Cong_GN_MJ.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_GN_MJ) as (_ & Cong_NG_MJ & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_GH_Cc) as Cong_Cc_GH.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_GN_Cc) as Cong_Cc_GN.
	pose proof (cn_congruencetransitive _ _ _ _ _ _ Cong_Cc_GN Cong_Cc_GH) as Cong_GN_GH.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_N_D) as BetS_D_N_G.
	pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_D_F_M BetS_F_M_J) as BetS_D_F_J.
	pose proof (lemma_betweennotequal _ _ _ BetS_F_M_J) as (_ & _ & neq_F_J).
	pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_D_F_M BetS_F_M_J) as BetS_D_M_J.

	pose proof (lemma_s_onray_assert_bets_AEB _ _ _ BetS_F_Q_J neq_F_J) as OnRay_FJ_Q.
	pose proof (lemma_s_onray _ _ _ _ BetS_D_F_G BetS_D_F_J) as OnRay_FG_J.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_FG_J) as OnRay_FJ_G.
	pose proof (lemma_layoffunique _ _ _ _ OnRay_FJ_Q OnRay_FJ_G Cong_FQ_FG) as eq_Q_G.
	pose proof (lemma_equalitysymmetric _ _ eq_Q_G) as eq_G_Q.
	assert (BetS F G J) as BetS_F_G_J by (rewrite eq_G_Q; exact BetS_F_Q_J).
	pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_D_F_G BetS_F_G_J) as BetS_D_G_J.
	pose proof (lemma_subtractequals _ _ _ _ _ BetS_D_N_G BetS_D_M_J Cong_NG_MJ BetS_D_G_J) as BetS_D_N_M.


	pose proof (postulate_Euclid3 _ _ neq_F_D) as (L & CI_L_F_F_D).
	pose proof (postulate_Euclid3 _ _ neq_G_H) as (R & CI_R_G_G_H).

	pose proof (lemma_s_outcirc_beyond_perimeter _ _ _ _ _ _ CI_L_F_F_D BetS_F_M_H Cong_FM_FD) as OutCirc_H_L.
	pose proof (lemma_ondiameter _ _ _ _ _ _ _ CI_L_F_F_D Cong_FD_FD Cong_FM_FD BetS_D_F_M BetS_D_N_M) as InCirc_N_L.

	pose proof (lemma_s_oncirc_radius _ _ _ _ _ CI_R_G_G_H Cong_GH_GH) as OnCirc_H_R.
	pose proof (lemma_s_oncirc_radius _ _ _ _ _ CI_R_G_G_H Cong_GN_GH) as OnCirc_N_R.

	pose proof (postulate_circle_circle _ _ _ _ _ _ _ _ _ _ CI_L_F_F_D InCirc_N_L OutCirc_H_L CI_R_G_G_H OnCirc_N_R OnCirc_H_R) as (K & OnCirc_K_L & OnCirc_K_R).

	pose proof (axiom_circle_center_radius _ _ _ _ _ CI_L_F_F_D OnCirc_K_L) as Cong_FK_FD.
	pose proof (axiom_circle_center_radius _ _ _ _ _ CI_R_G_G_H OnCirc_K_R) as Cong_GK_GH.

	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_FK_FD Cong_FD_Aa) as Cong_FK_Aa.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_GK_GH Cong_GH_Cc) as Cong_GK_Cc.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_FK_Aa) as Cong_Aa_FK.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_GK_Cc) as Cong_Cc_GK.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_FK_Aa) as (_ & Cong_KF_Aa & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_KF_Aa) as Cong_Aa_KF.

	pose proof (axiom_nocollapse _ _ _ _ neq_A_a Cong_Aa_FK) as neq_F_K.
	pose proof (axiom_nocollapse _ _ _ _ neq_C_c Cong_Cc_GK) as neq_G_K.


	assert (~ Col F G K) as n_Col_F_G_K.
	{
		intro Col_F_G_K.
		(* assert by cases *)
		assert (nCol F G K) as nCol_F_G_K.
		destruct Col_F_G_K as [eq_F_G | [eq_F_K | [eq_G_K | [BetS_G_F_K | [BetS_F_G_K | BetS_F_K_G]]]]].
		{
			(* case eq_F_G *)
			contradict eq_F_G.
			exact neq_F_G.
		}
		{
			(* case eq_F_K *)
			contradict eq_F_K.
			exact neq_F_K.
		}
		{
			(* case eq_G_K *)
			contradict eq_G_K.
			exact neq_G_K.
		}
		{
			(* case BetS_G_F_K *)
			destruct TogetherGreater_Aa_Bb_Cc as (S & BetS_A_a_S & Cong_aS_Bb & Lt_Cc_AS).
			pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_aS_Bb Cong_Bb_FG) as Cong_aS_FG.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_F_K) as BetS_K_F_G.
			pose proof (cn_sumofparts _ _ _ _ _ _ Cong_Aa_KF Cong_aS_FG BetS_A_a_S BetS_K_F_G) as Cong_AS_KG.
			pose proof (lemma_congruenceflip _ _ _ _ Cong_AS_KG) as (_ & _ & Cong_AS_GK).
			pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_Cc_AS Cong_AS_GK) as Lt_Cc_GK.
			pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_Cc_GK Cong_Cc_GK) as Lt_GK_GK.
			pose proof (lemma_trichotomy_asymmetric _ _ _ _ Lt_GK_GK) as n_Lt_GK_GK.

			contradict Lt_GK_GK.
			exact n_Lt_GK_GK.
		}
		{
			(* case BetS_F_G_K *)
			destruct TogetherGreater_Bb_Cc_Aa as (S & BetS_B_b_S & Cong_bS_Cc & Lt_Aa_BS).
			pose proof (lemma_congruencesymmetric _ _ _ _ Cong_bS_Cc) as Cong_Cc_bS.
			pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_GK_Cc Cong_Cc_bS) as Cong_GK_bS.
			pose proof (cn_sumofparts _ _ _ _ _ _ Cong_FG_Bb Cong_GK_bS BetS_F_G_K BetS_B_b_S) as Cong_FK_BS.
			pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_Aa_BS Cong_Aa_FK) as Lt_FK_BS.
			pose proof (lemma_congruencesymmetric _ _ _ _ Cong_FK_BS) as Cong_BS_FK.
			pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_FK_BS Cong_BS_FK) as Lt_FK_FK.
			pose proof (lemma_trichotomy_asymmetric _ _ _ _ Lt_FK_FK) as n_Lt_FK_FK.

			contradict Lt_FK_FK.
			exact n_Lt_FK_FK.
		}
		{
			(* case BetS_F_K_G *)

			destruct TogetherGreater_Aa_Cc_Bb as (S & BetS_A_a_S & Cong_aS_Cc & Lt_Bb_AS).
			pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_Bb_AS Cong_Bb_FG) as Lt_FG_AS.
			pose proof (lemma_congruencesymmetric _ _ _ _ Cong_aS_Cc) as Cong_Cc_aS.
			pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_GK_Cc Cong_Cc_aS) as Cong_GK_aS.
			pose proof (lemma_congruenceflip _ _ _ _ Cong_GK_aS) as (_ & Cong_KG_aS & _).
			pose proof (cn_sumofparts _ _ _ _ _ _ Cong_FK_Aa Cong_KG_aS BetS_F_K_G BetS_A_a_S) as Cong_FG_AS.
			pose proof (lemma_congruencesymmetric _ _ _ _ Cong_FG_AS) as Cong_AS_FG.
			pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_FG_AS Cong_AS_FG) as Lt_FG_FG.
			pose proof (lemma_trichotomy_asymmetric _ _ _ _ Lt_FG_FG) as n_Lt_FG_FG.

			contradict Lt_FG_FG.
			exact n_Lt_FG_FG.
		}
		pose proof (lemma_s_ncol_n_col _ _ _ nCol_F_G_K) as n_Col_F_G_K.

		contradict Col_F_G_K.
		exact n_Col_F_G_K.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_F_G_K) as nCol_F_G_K.

	pose proof (lemma_s_triangle _ _ _ nCol_F_G_K) as Triangle_FGK.

	exists G, K.
	split.
	exact Cong_FG_Bb.
	split.
	exact Cong_FK_Aa.
	split.
	exact Cong_GK_Cc.
	split.
	exact OnRay_FE_G.
	exact Triangle_FGK.
Qed.

End Euclid.
