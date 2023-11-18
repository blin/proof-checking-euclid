Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_flip.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_OnRay_orderofpoints_any.
Require Import ProofCheckingEuclid.by_prop_OnRay_shared_initial_point.
Require Import ProofCheckingEuclid.by_prop_Par_collinear2.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_10.
Require Import ProofCheckingEuclid.proposition_15a.
Require Import ProofCheckingEuclid.proposition_27B.
Require Import ProofCheckingEuclid.proposition_37.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_39A :
	forall A B C D M,
	Triangle A B C ->
	EqAreaTri A B C D B C ->
	BetS A M C ->
	OnRay B D M ->
	Par A D B C.
Proof.
	intros A B C D M.
	intros Triangle_ABC.
	intros EqAreaTri_ABC_DBC.
	intros BetS_A_M_C.
	intros OnRay_BD_M.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq B B) as eq_B_B by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C A B A eq_A_A) as Col_A_B_A.
	pose proof (by_def_Col_from_eq_B_C A B B eq_B_B) as Col_A_B_B.

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_ABC) as nCol_A_B_C.

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).

	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_C) as n_Col_A_B_C.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_B) as OnRay_CB_B.

	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_ABC_DBC) as EqAreaTri_DBC_ABC.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_M_C) as BetS_C_M_A.

	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_BD_M) as OnRay_BM_D.

	pose proof (proposition_10 _ _ neq_A_B) as (m & BetS_A_m_B & Cong_mA_mB).

	assert (eq m m) as eq_m_m by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C m C m eq_m_m) as Col_m_C_m.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_m_B) as BetS_B_m_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_m_B) as (neq_m_B & neq_A_m &_ ).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_m_A) as (neq_m_A & neq_B_m &_ ).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_m_B) as Col_A_m_B.
	pose proof (by_prop_Col_order _ _ _ Col_A_m_B) as (Col_m_A_B & Col_m_B_A & Col_B_A_m & Col_A_B_m & Col_B_m_A).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_mA_mB) as Cong_mB_mA.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_mB_mA) as (Cong_Bm_Am & _ & _).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_B_C Col_A_B_A Col_A_B_m neq_A_m) as nCol_A_m_C.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_m_C) as (_ & neq_m_C & _ & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_m_C) as (_ & nCol_m_C_A & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_m_C) as neq_C_m.

	pose proof (lemma_extension _ _ _ _ neq_C_m neq_m_C) as (H & BetS_C_m_H & Cong_mH_mC).

	assert (eq H H) as eq_H_H by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C H m H eq_H_H) as Col_H_m_H.
	pose proof (by_def_Col_from_eq_A_C A H A eq_A_A) as Col_A_H_A.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_m_H) as BetS_H_m_C.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_m_H) as (neq_m_H & _ & neq_C_H).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_H_m_C) as (_ & neq_H_m & neq_H_C).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_m_H) as Col_C_m_H.
	pose proof (by_prop_Col_order _ _ _ Col_C_m_H) as (Col_m_C_H & Col_m_H_C & Col_H_C_m & Col_C_H_m & Col_H_m_C).

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_C_m_H neq_C_m) as OnRay_Cm_H.
	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_H_m_C neq_H_m) as OnRay_Hm_C.

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_mH_mC) as Cong_mC_mH.


	assert (~ Col B A H) as n_Col_B_A_H.
	{
		intro Col_B_A_H.

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_A_H Col_B_A_m neq_B_A) as Col_A_H_m.
		pose proof (by_prop_Col_order _ _ _ Col_A_H_m) as (_ & Col_H_m_A & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_H_m_A Col_H_m_C neq_H_m) as Col_m_A_C.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_m_A_B Col_m_A_C neq_m_A) as Col_A_B_C.

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_B_A_H) as nCol_B_A_H.

	pose proof (postulate_Euclid5 _ _ _ _ _ _ BetS_C_m_H BetS_B_m_A BetS_C_M_A Cong_Bm_Am Cong_mC_mH nCol_B_A_H) as (E & BetS_B_M_E & BetS_H_A_E).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_M_E) as (_ & neq_B_M & _).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_H_A_E) as Col_H_A_E.
	pose proof (by_prop_Col_order _ _ _ Col_H_A_E) as (Col_A_H_E & _ & _ & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_H_A_E) as (neq_A_E & _ & _).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_m_C_A Col_m_C_m Col_m_C_H neq_m_H) as nCol_m_H_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_m_H_A) as (_ & _ & nCol_A_m_H & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_m_H_A) as (nCol_H_m_A & _ & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_m_H_A) as (_ & neq_H_A & _ & _ & _ & _).
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_H_m_A) as CongA_HmA_AmH.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_H_A) as OnRay_HA_A.

	pose proof (proposition_15a _ _ _ _ _ BetS_A_m_B BetS_H_m_C nCol_A_m_H) as CongA_AmH_CmB.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_HmA_AmH CongA_AmH_CmB) as CongA_HmA_CmB.

	pose proof (proposition_04 _ _ _ _ _ _ Cong_mH_mC Cong_mA_mB CongA_HmA_CmB) as (_ & CongA_mHA_mCB & _).

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_mHA_mCB OnRay_Cm_H OnRay_CB_B) as CongA_mHA_HCB.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_mHA_HCB) as CongA_HCB_mHA.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_HCB_mHA OnRay_Hm_C OnRay_HA_A) as CongA_HCB_CHA.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_HCB_CHA) as CongA_CHA_HCB.
	pose proof (by_prop_CongA_flip _ _ _ _ _ _ CongA_CHA_HCB) as CongA_AHC_BCH.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_AHC_BCH) as nCol_B_C_H.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_C_H) as CongA_BCH_HCB.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_AHC_BCH CongA_BCH_HCB) as CongA_AHC_HCB.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_H_m_A Col_H_m_H Col_H_m_C neq_H_C) as nCol_H_C_A.
	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_A_m_B Col_H_C_m nCol_H_C_A) as OppositeSide_A_HC_B.
	pose proof (proposition_27B _ _ _ _ CongA_AHC_HCB OppositeSide_A_HC_B) as Par_AH_CB.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AH_CB) as Par_CB_AH.

	pose proof (by_prop_Par_collinear2 _ _ _ _ _ _ Par_CB_AH Col_A_H_A Col_A_H_E neq_A_E) as Par_CB_AE.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_CB_AE) as Par_AE_CB.
	pose proof (by_prop_Par_flip _ _ _ _ Par_AE_CB) as (_ & Par_AE_BC & _).

	pose proof (proposition_37 _ _ _ _ Par_AE_BC) as EqAreaTri_ABC_EBC.
	pose proof (axiom_EqAreaTri_transitive _ _ _ _ _ _ _ _ _ EqAreaTri_DBC_ABC EqAreaTri_ABC_EBC) as EqAreaTri_DBC_EBC.
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_DBC_EBC) as EqAreaTri_EBC_DBC.

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_M_E neq_B_M) as OnRay_BM_E.

	pose proof (by_prop_OnRay_shared_initial_point _ _ _ _ OnRay_BM_D OnRay_BM_E) as OnRay_BD_E.

	(* assert by cases *)
	assert (Par A D B C) as Par_AD_BC.
	pose proof (by_prop_OnRay_orderofpoints_any _ _ _ OnRay_BD_E) as [BetS_B_E_D | [eq_D_E | BetS_B_D_E]].
	{
		(* case BetS_B_E_D *)
		pose proof (axiom_deZolt1 _ C _ _ BetS_B_E_D) as n_EqAreaTri_DBC_EBC.

		contradict EqAreaTri_DBC_EBC.
		exact n_EqAreaTri_DBC_EBC.
	}
	{
		(* case eq_D_E *)
		assert (Par A D B C) as Par_AD_BC by (rewrite eq_D_E; exact Par_AE_BC).

		exact Par_AD_BC.
	}
	{
		(* case BetS_B_D_E *)
		pose proof (axiom_deZolt1 _ C _ _ BetS_B_D_E) as n_EqAreaTri_EBC_DBC.

		contradict EqAreaTri_EBC_DBC.
		exact n_EqAreaTri_EBC_DBC.
	}

	exact Par_AD_BC.
Qed.

End Euclid.
