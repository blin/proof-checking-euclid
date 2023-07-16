Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.by_def_LtA.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.proposition_03.
Require Import ProofCheckingEuclid.proposition_04.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_angleorderrespectscongruence :
	forall A B C D E F a b c,
	LtA A B C D E F ->
	CongA a b c D E F ->
	LtA A B C a b c.
Proof.
	intros A B C D E F a b c.
	intros LtA_ABC_DEF.
	intros CongA_abc_DEF.

	destruct LtA_ABC_DEF as (G & H & J & BetS_G_H_J & OnRay_ED_G & OnRay_EF_J & CongA_ABC_DEH).

	pose proof (lemma_betweennotequal _ _ _ BetS_G_H_J) as (_ & _ & neq_G_J).
	pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_G_H_J neq_G_J) as OnRay_GJ_H.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_G_J) as OnRay_GJ_J.

	pose proof (cn_congruencereflexive G H) as Cong_GH_GH.
	pose proof (by_def_Lt _ _ _ _ _ BetS_G_H_J Cong_GH_GH) as Lt_GH_GJ.

	pose proof (lemma_onray_strict _ _ _ OnRay_ED_G) as neq_E_G.
	pose proof (lemma_onray_strict _ _ _ OnRay_EF_J) as neq_E_J.

	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_ABC_DEH) as (_ & _ & _ & _ & neq_E_H & _).
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_E_H) as OnRay_EH_H.

	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_abc_DEF) as (neq_a_b & neq_b_c & _ & _ & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_a_b) as neq_b_a.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_abc_DEF) as CongA_DEF_abc.

	pose proof (lemma_layoff _ _ _ _ neq_b_a neq_E_G) as (U & OnRay_ba_U & Cong_bU_EG).
	pose proof (lemma_layoff _ _ _ _ neq_b_c neq_E_J) as (V & OnRay_bc_V & Cong_bV_EJ).

	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_ba_U) as OnRay_bU_a.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_bU_EG) as Cong_EG_bU.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_bV_EJ) as Cong_EJ_bV.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_EG_bU) as (Cong_GE_Ub & _ & _).

	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_DEF_abc OnRay_ba_U OnRay_bc_V) as CongA_DEF_UbV.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_DEF_UbV) as CongA_UbV_DEF.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_UbV_DEF OnRay_ED_G OnRay_EF_J) as CongA_UbV_GEJ.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_UbV_GEJ) as CongA_GEJ_UbV.

	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_DEF_UbV) as nCol_U_b_V.
	pose proof (lemma_NCdistinct _ _ _ nCol_U_b_V) as (neq_U_b & neq_b_V & _ & neq_b_U & neq_V_b & neq_V_U).
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_U_b) as OnRay_Ub_b.

	pose proof (proposition_04 _ _ _ _ _ _ Cong_EG_bU Cong_EJ_bV CongA_GEJ_UbV) as (Cong_GJ_UV & CongA_EGJ_bUV & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_GJ_UV) as Cong_UV_GJ.
	pose proof (proposition_03 _ _ _ _ _ _ Lt_GH_GJ Cong_UV_GJ) as (W & BetS_U_W_V & Cong_UW_GH).

	pose proof (lemma_betweennotequal _ _ _ BetS_U_W_V) as (_ & _ & neq_U_V).
	pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_U_W_V neq_U_V) as OnRay_UV_W.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_U_V) as OnRay_UV_V.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_UW_GH) as Cong_GH_UW.

	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_ABC_DEH OnRay_ED_G OnRay_EH_H) as CongA_ABC_GEH.

	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_ABC_GEH) as nCol_G_E_H.
	pose proof (lemma_NCorder _ _ _ nCol_G_E_H) as (_ & _ & nCol_H_G_E & _ & _).

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_H_G_E) as CongA_HGE_EGH.
	pose proof (lemma_NCdistinct _ _ _ nCol_G_E_H) as (neq_G_E & _ & _ & _ & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_G_E) as OnRay_GE_E.

	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_EGJ_bUV OnRay_Ub_b OnRay_UV_W) as CongA_EGJ_bUW.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_EGJ_bUW) as CongA_bUW_EGJ.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_bUW_EGJ OnRay_GE_E OnRay_GJ_H) as CongA_bUW_EGH.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_bUW_EGH) as CongA_EGH_bUW.

	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_EGH_bUW) as nCol_b_U_W.
	pose proof (lemma_NCdistinct _ _ _ nCol_b_U_W) as (_ & _ & neq_b_W & _ & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_b_W) as OnRay_bW_W.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_b_U_W) as CongA_bUW_WUb.

	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_EGH_bUW CongA_bUW_WUb) as CongA_EGH_WUb.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_HGE_EGH CongA_EGH_WUb) as CongA_HGE_WUb.
	pose proof (proposition_04 _ _ _ _ _ _ Cong_GH_UW Cong_GE_Ub CongA_HGE_WUb) as (_ & _ & CongA_GEH_UbW).
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_ABC_GEH CongA_GEH_UbW) as CongA_ABC_UbW.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_ABC_UbW OnRay_bU_a OnRay_bW_W) as CongA_ABC_abW.

	pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_U_W_V OnRay_ba_U OnRay_bc_V CongA_ABC_abW) as LtA_ABC_abc.

	exact LtA_ABC_abc.
Qed.

End Euclid.
