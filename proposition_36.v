Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear2.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_crisscross.
Require Import ProofCheckingEuclid.proposition_33.
Require Import ProofCheckingEuclid.proposition_34.
Require Import ProofCheckingEuclid.proposition_35.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_36 :
	forall A B C D E F G H,
	Parallelogram A B C D ->
	Parallelogram E F G H ->
	Col A D E ->
	Col A D H ->
	Col B C F ->
	Col B C G ->
	Cong B C F G ->
	EqAreaQuad A B C D E F G H.
Proof.
	intros A B C D E F G H.
	intros Parallelogram_A_B_C_D.
	intros Parallelogram_E_F_G_H.
	intros Col_A_D_E.
	intros Col_A_D_H.
	intros Col_B_C_F.
	intros Col_B_C_G.
	intros Cong_BC_FG.

	assert (Parallelogram_A_B_C_D_2 := Parallelogram_A_B_C_D).
	destruct Parallelogram_A_B_C_D_2 as (Par_AB_CD & Par_AD_BC).

	assert (Parallelogram_E_F_G_H_2 := Parallelogram_E_F_G_H).
	destruct Parallelogram_E_F_G_H_2 as (Par_EF_GH & Par_EH_FG).

	pose proof (proposition_34 _ _ _ _ Parallelogram_E_F_G_H) as (Cong_EH_FG & Cong_EF_HG & CongA_FEH_HGF & CongA_EHG_GFE & CongTriangles_FEH_HGF).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_EH_FG) as Cong_FG_EH.

	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_CD) as (Par_BA_CD & Par_AB_DC & Par_BA_DC).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AB_CD) as Par_CD_AB.
	pose proof (by_prop_Par_flip _ _ _ _ Par_CD_AB) as (Par_DC_AB & Par_CD_BA & Par_DC_BA).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (nCol_A_B_C & nCol_A_C_D & nCol_B_C_D & nCol_A_B_D).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (_ & neq_B_C & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_B_C) as neq_C_B.

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AD_BC) as Par_BC_AD.

	pose proof (by_prop_Par_flip _ _ _ _ Par_EF_GH) as (Par_FE_GH & Par_EF_HG & Par_FE_HG).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_EF_GH) as Par_GH_EF.
	pose proof (by_prop_Par_flip _ _ _ _ Par_GH_EF) as (Par_HG_EF & Par_GH_FE & Par_HG_FE).
	pose proof (by_prop_Par_NC _ _ _ _ Par_EF_GH) as (nCol_E_F_G & nCol_E_G_H & nCol_F_G_H & nCol_E_F_H).

	pose proof (by_prop_Par_flip _ _ _ _ Par_EH_FG) as (Par_HE_FG & Par_EH_GF & Par_HE_GF).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_EH_FG) as Par_FG_EH.
	pose proof (by_prop_Par_flip _ _ _ _ Par_FG_EH) as (Par_GF_EH & Par_FG_HE & Par_GF_HE).
	pose proof (by_prop_Par_NC _ _ _ _ Par_EH_FG) as (nCol_E_H_F & _ & nCol_H_F_G & nCol_E_H_G).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_E_H_F) as (neq_E_H & neq_H_F & neq_E_F & neq_H_E & neq_F_H & neq_F_E).

	pose proof (by_prop_Col_order _ _ _ Col_B_C_F) as (Col_C_B_F & Col_C_F_B & Col_F_B_C & Col_B_F_C & Col_F_C_B).
	pose proof (by_prop_Col_order _ _ _ Col_B_C_G) as (Col_C_B_G & Col_C_G_B & Col_G_B_C & Col_B_G_C & Col_G_C_B).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_C_F Col_B_C_G neq_B_C) as Col_C_F_G.
	pose proof (by_prop_Col_order _ _ _ Col_C_F_G) as (_ & _ & _ & _ & Col_G_F_C).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_B_F Col_C_B_G neq_C_B) as Col_B_F_G.
	pose proof (by_prop_Col_order _ _ _ Col_B_F_G) as (_ & _ & _ & _ & Col_G_F_B).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_C_G Col_B_C_F neq_B_C) as Col_C_G_F.
	pose proof (by_prop_Col_order _ _ _ Col_C_G_F) as (_ & _ & _ & _ & Col_F_G_C).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_B_G Col_C_B_F neq_C_B) as Col_B_G_F.
	pose proof (by_prop_Col_order _ _ _ Col_B_G_F) as (_ & _ & _ & _ & Col_F_G_B).

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_BC_FG Cong_FG_EH) as Cong_BC_EH.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BC_EH) as Cong_EH_BC.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_EH_BC) as (_ & Cong_HE_BC & _).

	pose proof (by_prop_Par_collinear2 _ _ _ _ _ _ Par_BC_AD Col_A_D_E Col_A_D_H neq_E_H) as Par_BC_EH.
	pose proof (by_prop_Par_flip _ _ _ _ Par_BC_EH) as (Par_CB_EH & Par_BC_HE & Par_CB_HE).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_BC_EH) as Par_EH_BC.
	pose proof (by_prop_Par_flip _ _ _ _ Par_EH_BC) as (Par_HE_BC & Par_EH_CB & Par_HE_CB).
	pose proof (by_prop_Par_NC _ _ _ _ Par_BC_EH) as (nCol_B_C_E & nCol_B_E_H & nCol_C_E_H & nCol_B_C_H).

	pose proof (by_def_Parallelogram _ _ _ _ Par_GH_EF Par_GF_HE) as Parallelogram_G_H_E_F.
	pose proof (by_def_Parallelogram _ _ _ _ Par_FE_HG Par_FG_EH) as Parallelogram_F_E_H_G.

	assert (~ ~ (Cross E C B H \/ Cross E B H C)) as n_n_Cross_EC_BH_or_Cross_EB_HC.
	{
		intro n_Cross_EC_BH_or_Cross_EB_HC.

		apply Classical_Prop.not_or_and in n_Cross_EC_BH_or_Cross_EB_HC .
		destruct n_Cross_EC_BH_or_Cross_EB_HC as (n_Cross_EC_BH & n_Cross_EB_HC).

		pose proof (lemma_crisscross _ _ _ _ Par_EH_BC n_Cross_EB_HC) as Cross_EC_BH.

		contradict Cross_EC_BH.
		exact n_Cross_EC_BH.
	}
	assert (Cross_EC_BH_or_Cross_EB_HC := n_n_Cross_EC_BH_or_Cross_EB_HC).
	apply Classical_Prop.NNPP in Cross_EC_BH_or_Cross_EB_HC.


	(* assert by cases *)
	assert (EqAreaQuad A B C D E F G H) as EqAreaQuad_ABCD_EFGH.
	destruct Cross_EC_BH_or_Cross_EB_HC as [Cross_EC_BH | Cross_EB_HC].
	{
		(* case Cross_EC_BH *)

		destruct Cross_EC_BH as (M & BetS_E_M_C & BetS_B_M_H).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_H) as BetS_H_M_B.

		pose proof (proposition_33 _ _ _ _ _ Par_EH_BC Cong_EH_BC BetS_E_M_C BetS_H_M_B) as (Par_EB_HC & Cong_EB_HC).

		pose proof (by_prop_Par_flip _ _ _ _ Par_EB_HC) as (Par_BE_HC & Par_EB_CH & Par_BE_CH).
		pose proof (by_prop_Par_symmetric _ _ _ _ Par_EB_HC) as Par_HC_EB.
		pose proof (by_prop_Par_flip _ _ _ _ Par_HC_EB) as (Par_CH_EB & Par_HC_BE & Par_CH_BE).

		pose proof (by_def_Parallelogram _ _ _ _ Par_EB_CH Par_EH_BC) as Parallelogram_E_B_C_H.
		pose proof (by_def_Parallelogram _ _ _ _ Par_CH_EB Par_CB_HE) as Parallelogram_C_H_E_B.

		pose proof (proposition_35 _ _ _ _ _ _ Parallelogram_A_B_C_D Parallelogram_E_B_C_H Col_A_D_E Col_A_D_H) as EqAreaQuad_ABCD_EBCH.
		pose proof (proposition_35 _ _ _ _ _ _ Parallelogram_G_H_E_F Parallelogram_C_H_E_B Col_G_F_C Col_G_F_B) as EqAreaQuad_GHEF_CHEB.

		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_GHEF_CHEB) as (_ & _ & EqAreaQuad_GHEF_EBCH & _ & _ & _ & _).
		pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_GHEF_EBCH) as EqAreaQuad_EBCH_GHEF.
		pose proof (axiom_EqAreaQuad_transitive _ _ _ _ _ _ _ _ _ _ _ _ EqAreaQuad_ABCD_EBCH EqAreaQuad_EBCH_GHEF) as EqAreaQuad_ABCD_GHEF.
		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_ABCD_GHEF) as (_ & _ & EqAreaQuad_ABCD_EFGH & _ & _ & _ & _).

		exact EqAreaQuad_ABCD_EFGH.
	}
	{
		(* case Cross_EB_HC *)

		destruct Cross_EB_HC as (M & BetS_E_M_B & BetS_H_M_C).

		pose proof (proposition_33 _ _ _ _ _ Par_HE_BC Cong_HE_BC BetS_H_M_C BetS_E_M_B) as (Par_HB_EC & Cong_HB_EC).

		pose proof (by_prop_Par_flip _ _ _ _ Par_HB_EC) as (Par_BH_EC & Par_HB_CE & Par_BH_CE).
		pose proof (by_prop_Par_symmetric _ _ _ _ Par_HB_EC) as Par_EC_HB.
		pose proof (by_prop_Par_flip _ _ _ _ Par_EC_HB) as (Par_CE_HB & Par_EC_BH & Par_CE_BH).

		pose proof (by_def_Parallelogram _ _ _ _ Par_HB_CE Par_HE_BC) as Parallelogram_H_B_C_E.
		pose proof (by_def_Parallelogram _ _ _ _ Par_CE_HB Par_CB_EH) as Parallelogram_C_E_H_B.

		pose proof (proposition_35 _ _ _ _ _ _ Parallelogram_A_B_C_D Parallelogram_H_B_C_E Col_A_D_H Col_A_D_E) as EqAreaQuad_ABCD_HBCE.
		pose proof (proposition_35 _ _ _ _ _ _ Parallelogram_F_E_H_G Parallelogram_C_E_H_B Col_F_G_C Col_F_G_B) as EqAreaQuad_FEHG_CEHB.

		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_FEHG_CEHB) as (_ & _ & EqAreaQuad_FEHG_HBCE & _ & _ & _ & _).
		pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_FEHG_HBCE) as EqAreaQuad_HBCE_FEHG.
		pose proof (axiom_EqAreaQuad_transitive _ _ _ _ _ _ _ _ _ _ _ _ EqAreaQuad_ABCD_HBCE EqAreaQuad_HBCE_FEHG) as EqAreaQuad_ABCD_FEHG.
		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_ABCD_FEHG) as (_ & _ & _ & EqAreaQuad_ABCD_EFGH & _ & _ & _).

		exact EqAreaQuad_ABCD_EFGH.
	}

	exact EqAreaQuad_ABCD_EFGH.
Qed.

End Euclid.
