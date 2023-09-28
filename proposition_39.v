Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_CongA_flip.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_SameSide_flip.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_angletrichotomy_n_CongA_ABC_DEF_n_LtA_DEF_ABC_LtA_ABC_DEF.
Require Import ProofCheckingEuclid.lemma_crossbar_LtA.
Require Import ProofCheckingEuclid.proposition_07.
Require Import ProofCheckingEuclid.proposition_26A.
Require Import ProofCheckingEuclid.proposition_39A.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_39 :
	forall A B C D,
	Triangle A B C ->
	Triangle D B C ->
	SameSide A D B C ->
	EqAreaTri A B C D B C ->
	neq A D ->
	Par A D B C.
Proof.
	intros A B C D.
	intros Triangle_ABC.
	intros Triangle_DBC.
	intros SameSide_A_D_BC.
	intros EqAreaTri_A_B_C_D_B_C.
	intros neq_A_D.

	pose proof (cn_congruencereflexive B C) as Cong_BC_BC.

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_ABC) as nCol_A_B_C.
	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_DBC) as nCol_D_B_C.

	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).

	pose proof (by_prop_nCol_order _ _ _ nCol_D_B_C) as (nCol_B_D_C & nCol_B_C_D & nCol_C_D_B & nCol_D_C_B & nCol_C_B_D).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_D_B_C) as (neq_D_B & _ & neq_D_C & neq_B_D & _ & neq_C_D).

	pose proof (by_def_Triangle _ _ _ nCol_A_C_B) as Triangle_ACB.
	pose proof (by_def_Triangle _ _ _ nCol_D_C_B) as Triangle_DCB.

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_A_D_BC) as (SameSide_D_A_BC & _ & _).
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_A_D_BC) as SameSide_A_D_CB.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_A_D_CB) as (SameSide_D_A_CB & _ & _).

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_C) as OnRay_BC_C.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_A) as OnRay_BA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_D) as OnRay_BD_D.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_B) as OnRay_CB_B.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_A) as OnRay_CA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_D) as OnRay_CD_D.

	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_A_B_C_D_B_C) as (_ & EqAreaTri_A_B_C_D_C_B & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_A_B_C_D_C_B) as EqAreaTri_D_C_B_A_B_C.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_D_C_B_A_B_C) as (_ & EqAreaTri_D_C_B_A_C_B & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_D_C_B_A_C_B) as EqAreaTri_A_C_B_D_C_B.
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_A_B_C_D_B_C) as EqAreaTri_D_B_C_A_B_C.

	assert (~ ~ Par A D B C) as n_n_Par_AD_BC.
	{
		intro n_Par_AD_BC.

		assert (~ LtA C B D C B A) as n_LtA_CBD_CBA.
		{
			intro LtA_CBD_CBA.

			pose proof (lemma_crossbar_LtA _ _ _ _ _ _ LtA_CBD_CBA SameSide_D_A_BC OnRay_BC_C OnRay_BA_A) as (M & BetS_A_M_C & OnRay_BD_M).
			pose proof (proposition_39A _ _ _ _ _ Triangle_ABC EqAreaTri_A_B_C_D_B_C BetS_A_M_C OnRay_BD_M) as Par_AD_BC.

			contradict Par_AD_BC.
			exact n_Par_AD_BC.
		}


		assert (~ LtA C B A C B D) as n_LtA_CBA_CBD.
		{
			intro LtA_CBA_CBD.

			pose proof (lemma_crossbar_LtA _ _ _ _ _ _ LtA_CBA_CBD SameSide_A_D_BC OnRay_BC_C OnRay_BD_D) as (M & BetS_D_M_C & OnRay_BA_M).
			pose proof (proposition_39A _ _ _ _ _ Triangle_DBC EqAreaTri_D_B_C_A_B_C BetS_D_M_C OnRay_BA_M) as Par_DA_BC.
			pose proof (by_prop_Par_flip _ _ _ _ Par_DA_BC) as (Par_AD_BC & _ & _).

			contradict Par_AD_BC.
			exact n_Par_AD_BC.
		}


		assert (~ ~ CongA C B D C B A) as n_n_CongA_CBD_CBA.
		{
			intro n_CongA_CBD_CBA.

			pose proof (lemma_angletrichotomy_n_CongA_ABC_DEF_n_LtA_DEF_ABC_LtA_ABC_DEF _ _ _ _ _ _ nCol_C_B_D nCol_C_B_A n_CongA_CBD_CBA n_LtA_CBA_CBD) as LtA_CBD_CBA.

			contradict LtA_CBD_CBA.
			exact n_LtA_CBD_CBA.
		}
		assert (CongA_CBD_CBA := n_n_CongA_CBD_CBA).
		apply Classical_Prop.NNPP in CongA_CBD_CBA.

		pose proof (by_prop_CongA_flip _ _ _ _ _ _ CongA_CBD_CBA) as CongA_DBC_ABC.
		pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_DBC_ABC) as CongA_ABC_DBC.


		assert (~ LtA B C D B C A) as n_LtA_BCD_BCA.
		{
			intro LtA_BCD_BCA.

			pose proof (lemma_crossbar_LtA _ _ _ _ _ _ LtA_BCD_BCA SameSide_D_A_CB OnRay_CB_B OnRay_CA_A) as (M & BetS_A_M_B & OnRay_CD_M).
			pose proof (proposition_39A _ _ _ _ _ Triangle_ACB EqAreaTri_A_C_B_D_C_B BetS_A_M_B OnRay_CD_M) as Par_AD_CB.
			pose proof (by_prop_Par_flip _ _ _ _ Par_AD_CB) as (_ & Par_AD_BC & _).

			contradict Par_AD_BC.
			exact n_Par_AD_BC.
		}


		assert (~ LtA B C A B C D) as n_LtA_BCA_BCD.
		{
			intro LtA_BCA_BCD.

			pose proof (lemma_crossbar_LtA _ _ _ _ _ _ LtA_BCA_BCD SameSide_A_D_CB OnRay_CB_B OnRay_CD_D) as (M & BetS_D_M_B & OnRay_CA_M).
			pose proof (proposition_39A _ _ _ _ _ Triangle_DCB EqAreaTri_D_C_B_A_C_B BetS_D_M_B OnRay_CA_M) as Par_DA_CB.
			pose proof (by_prop_Par_flip _ _ _ _ Par_DA_CB) as (_ & _ & Par_AD_BC).

			contradict Par_AD_BC.
			exact n_Par_AD_BC.
		}


		assert (~ ~ CongA B C D B C A) as n_n_CongA_BCD_BCA.
		{
			intro n_CongA_BCD_BCA.

			pose proof (lemma_angletrichotomy_n_CongA_ABC_DEF_n_LtA_DEF_ABC_LtA_ABC_DEF _ _ _ _ _ _ nCol_B_C_D nCol_B_C_A n_CongA_BCD_BCA n_LtA_BCA_BCD) as LtA_BCD_BCA.

			contradict LtA_BCD_BCA.
			exact n_LtA_BCD_BCA.
		}
		assert (CongA_BCD_BCA := n_n_CongA_BCD_BCA).
		apply Classical_Prop.NNPP in CongA_BCD_BCA.

		pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_BCD_BCA) as CongA_BCA_BCD.

		pose proof (proposition_26A _ _ _ _ _ _ Triangle_ABC Triangle_DBC CongA_ABC_DBC CongA_BCA_BCD Cong_BC_BC) as (Cong_AB_DB & Cong_AC_DC & CongA_BAC_BDC).
		pose proof (proposition_07 _ _ _ _ neq_B_C Cong_AB_DB Cong_AC_DC SameSide_A_D_BC) as eq_A_D.

		contradict eq_A_D.
		exact neq_A_D.
	}
	assert (Par_AD_BC := n_n_Par_AD_BC).
	apply Classical_Prop.NNPP in Par_AD_BC.

	exact Par_AD_BC.
Qed.

End Euclid.
