Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_crossbar.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_shared_initial_point.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.lemma_sameside_onray_EFAC_BFG_EGAC.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_07.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_crossbar_LtA :
	forall A G H P S T,
	LtA H G A H G P ->
	SameSide A P G H ->
	OnRay G H S ->
	OnRay G P T ->
	exists X, BetS T X S /\ OnRay G A X.
Proof.
	intros A G H P S T.
	intros LtA_HGA_HGP.
	intros SameSide_A_P_GH.
	intros OnRay_GH_S.
	intros OnRay_GP_T.

	assert (eq G G) as eq_G_G by (reflexivity).

	pose proof (lemma_s_col_eq_A_B G G H eq_G_G) as Col_G_G_H.
	pose proof (cn_congruencereflexive G H) as Cong_GH_GH.

	destruct LtA_HGA_HGP as (L & K & J & BetS_L_K_J & OnRay_GH_L & OnRay_GP_J & CongA_HGA_HGK).

	pose proof (lemma_onray_strict _ _ _ OnRay_GH_L) as neq_G_L.
	pose proof (lemma_inequalitysymmetric _ _ neq_G_L) as neq_L_G.
	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_GH_L) as Col_G_H_L.
	pose proof (lemma_collinearorder _ _ _ Col_G_H_L) as (Col_H_G_L & Col_H_L_G & Col_L_G_H & Col_G_L_H & Col_L_H_G).

	pose proof (lemma_onray_strict _ _ _ OnRay_GP_J) as neq_G_J.
	pose proof (lemma_inequalitysymmetric _ _ neq_G_J) as neq_J_G.
	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_GP_J) as Col_G_P_J.
	pose proof (lemma_collinearorder _ _ _ Col_G_P_J) as (_ & _ & Col_J_G_P & _ & _).

	pose proof (lemma_onray_shared_initial_point _ _ _ _ OnRay_GP_J OnRay_GP_T) as OnRay_GJ_T.
	pose proof (lemma_onray_shared_initial_point _ _ _ _ OnRay_GH_L OnRay_GH_S) as OnRay_GL_S.

	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_HGA_HGK) as nCol_H_G_K.
	pose proof (lemma_NCorder _ _ _ nCol_H_G_K) as (nCol_G_H_K & nCol_G_K_H & nCol_K_H_G & nCol_H_K_G & nCol_K_G_H).
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_HGA_HGK) as CongA_HGK_HGA.
	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_HGA_HGK) as (_ & neq_G_A & _ & _ & _ & _).

	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_HGK_HGA) as nCol_H_G_A.
	pose proof (lemma_NCorder _ _ _ nCol_H_G_A) as (nCol_G_H_A & nCol_G_A_H & nCol_A_H_G & nCol_H_A_G & nCol_A_G_H).
	pose proof (lemma_equalanglesreflexive _ _ _ nCol_H_G_A) as CongA_HGA_HGA.

	assert (SameSide_A_P_GH_2 := SameSide_A_P_GH).
	destruct SameSide_A_P_GH_2 as (_ & _ & _ & _ & _ & _ & _ &  _ & nCol_G_H_P).
	pose proof (lemma_NCorder _ _ _ nCol_G_H_P) as (nCol_H_G_P & nCol_H_P_G & nCol_P_G_H & nCol_G_P_H & nCol_P_H_G).
	pose proof (lemma_NCdistinct _ _ _ nCol_G_H_P) as (neq_G_H & neq_H_P & neq_G_P & neq_H_G & neq_P_H & neq_P_G).

	pose proof (lemma_s_onray_assert_ABB _ _ neq_G_H) as OnRay_GH_H.

	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_GH_S) as Col_G_H_S.
	pose proof (lemma_collinearorder _ _ _ Col_G_H_S) as (_ & _ & _ & Col_G_S_H & _).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_G_H_P Col_G_H_L neq_G_L) as nCol_G_L_P.
	pose proof (lemma_NCorder _ _ _ nCol_G_L_P) as (nCol_L_G_P & nCol_L_P_G & nCol_P_G_L & nCol_G_P_L & nCol_P_L_G).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_G_P_H Col_G_P_J neq_G_J) as nCol_G_J_H.
	pose proof (lemma_NCorder _ _ _ nCol_G_J_H) as (nCol_J_G_H & nCol_J_H_G & nCol_H_G_J & nCol_G_H_J & nCol_H_J_G).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_G_H_J Col_G_H_L neq_G_L) as nCol_G_L_J.
	pose proof (lemma_NCorder _ _ _ nCol_G_L_J) as (nCol_L_G_J & nCol_L_J_G & nCol_J_G_L & nCol_G_J_L & nCol_J_L_G).

	pose proof (by_def_Triangle _ _ _ nCol_L_G_J) as Triangle_LGJ.

	pose proof (lemma_crossbar _ _ _ _ _ _ Triangle_LGJ BetS_L_K_J OnRay_GL_S OnRay_GJ_T) as (M & OnRay_GK_M & BetS_S_M_T).

	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_GK_M) as OnRay_GM_K.
	pose proof (lemma_onray_strict _ _ _ OnRay_GK_M) as neq_G_M.
	pose proof (lemma_inequalitysymmetric _ _ neq_G_M) as neq_M_G.

	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_GK_M) as Col_G_K_M.
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_G_K_H Col_G_K_M neq_G_M) as nCol_G_M_H.
	pose proof (lemma_NCorder _ _ _ nCol_G_M_H) as (nCol_M_G_H & nCol_M_H_G & nCol_H_G_M & nCol_G_H_M & nCol_H_M_G).
	pose proof (lemma_equalanglesreflexive _ _ _ nCol_H_G_M) as CongA_HGM_HGM.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_HGM_HGM OnRay_GH_H OnRay_GM_K) as CongA_HGM_HGK.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_HGM_HGK CongA_HGK_HGA) as CongA_HGM_HGA.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_S_M_T) as BetS_T_M_S.
	pose proof (lemma_betweennotequal _ _ _ BetS_S_M_T) as (_ & neq_S_M & _).

	pose proof (lemma_s_onray_assert_bets_ABE _ _ _ BetS_S_M_T neq_S_M) as OnRay_SM_T.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_SM_T) as OnRay_ST_M.

	pose proof (lemma_layoff _ _ _ _ neq_G_A neq_G_M) as (N & OnRay_GA_N & Cong_GN_GM).

	pose proof (lemma_congruenceflip _ _ _ _ Cong_GN_GM) as (Cong_NG_MG & _ & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_NG_MG) as Cong_MG_NG.

	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_HGA_HGA OnRay_GH_H OnRay_GA_N) as CongA_HGA_HGN.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_HGM_HGA CongA_HGA_HGN) as CongA_HGM_HGN.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_HGM_HGN) as CongA_HGN_HGM.
	pose proof (proposition_04 _ _ _ _ _ _ Cong_GH_GH Cong_GN_GM CongA_HGN_HGM) as (Cong_HN_HM & _ & _).

	pose proof (lemma_congruenceflip _ _ _ _ Cong_HN_HM) as (Cong_NH_MH & _ & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_NH_MH) as Cong_MH_NH.

	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_A_P_GH Col_G_G_H OnRay_GP_T) as SameSide_A_T_GH.
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_A_T_GH Col_G_S_H OnRay_ST_M) as SameSide_A_M_GH.
	pose proof (lemma_samesidesymmetric _ _ _ _ SameSide_A_M_GH) as (SameSide_M_A_GH & _ & _).
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_M_A_GH Col_G_G_H OnRay_GA_N) as SameSide_M_N_GH.

	pose proof (proposition_07 _ _ _ _ neq_G_H Cong_MG_NG Cong_MH_NH SameSide_M_N_GH) as eq_M_N.

	assert (OnRay G A M) as OnRay_GA_M by (rewrite eq_M_N; exact OnRay_GA_N).

	exists M.
	split.
	exact BetS_T_M_S.
	exact OnRay_GA_M.
Qed.

End Euclid.
