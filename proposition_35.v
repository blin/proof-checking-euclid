Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_Par.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_EqAreaQuad_reflexive.
Require Import ProofCheckingEuclid.by_prop_Lt_asymmetric.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_Lt_transitive.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_diagonalsmeet.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_parallelPasch.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.proposition_34.
Require Import ProofCheckingEuclid.proposition_35A.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_35 :
	forall A B C D E F,
	Parallelogram A B C D ->
	Parallelogram E B C F ->
	Col A D E ->
	Col A D F ->
	EqAreaQuad A B C D E B C F.
Proof.
	intros A B C D E F.
	intros Parallelogram_A_B_C_D.
	intros Parallelogram_E_B_C_F.
	intros Col_A_D_E.
	intros Col_A_D_F.

	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq D D) as eq_D_D by (reflexivity).

	pose proof (cn_congruencereflexive A E) as Cong_AE_AE.
	pose proof (cn_congruencereflexive A F) as Cong_AF_AF.
	pose proof (cn_congruencereflexive D E) as Cong_DE_DE.
	pose proof (cn_congruencereflexive D F) as Cong_DF_DF.
	pose proof (cn_congruencereflexive E F) as Cong_EF_EF.
	pose proof (cn_congruencereflexive F E) as Cong_FE_FE.
	pose proof (cn_congruencereverse D A) as Cong_DA_AD.
	pose proof (cn_congruencereverse E D) as Cong_ED_DE.
	pose proof (cn_congruencereverse E F) as Cong_EF_FE.
	pose proof (cn_congruencereverse F D) as Cong_FD_DF.
	pose proof (cn_congruencereverse F E) as Cong_FE_EF.

	pose proof (by_def_Col_from_eq_A_C C D C eq_C_C) as Col_C_D_C.
	pose proof (by_def_Col_from_eq_B_C A D D eq_D_D) as Col_A_D_D.
	pose proof (by_def_Col_from_eq_B_C D A A eq_A_A) as Col_D_A_A.

	assert (Parallelogram_A_B_C_D_2 := Parallelogram_A_B_C_D).
	destruct Parallelogram_A_B_C_D_2 as (Par_AB_CD & Par_AD_BC).

	pose proof (proposition_34 _ _ _ _ Parallelogram_A_B_C_D) as (Cong_AD_BC & Cong_AB_DC & CongA_BAD_DCB & CongA_ADC_CBA & CongTriangles_BAD_DCB).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AD_BC) as (Cong_DA_CB & Cong_DA_BC & Cong_AD_CB).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AD_BC) as Cong_BC_AD.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BC_AD) as (Cong_CB_DA & Cong_CB_AD & Cong_BC_DA).

	assert (Parallelogram_E_B_C_F_2 := Parallelogram_E_B_C_F).
	destruct Parallelogram_E_B_C_F_2 as (Par_EB_CF & Par_EF_BC).

	pose proof (proposition_34 _ _ _ _ Parallelogram_E_B_C_F) as (Cong_EF_BC & Cong_EB_FC & CongA_BEF_FCB & CongA_EFC_CBE & CongTriangles_BEF_FCB).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_EF_BC) as (Cong_FE_CB & Cong_FE_BC & Cong_EF_CB).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_EF_BC) as Cong_BC_EF.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BC_EF) as (Cong_CB_FE & Cong_CB_EF & Cong_BC_FE).

	pose proof (by_prop_Col_order _ _ _ Col_A_D_E) as (Col_D_A_E & Col_D_E_A & Col_E_A_D & Col_A_E_D & Col_E_D_A).
	pose proof (by_prop_Col_order _ _ _ Col_A_D_F) as (Col_D_A_F & Col_D_F_A & Col_F_A_D & Col_A_F_D & Col_F_D_A).


	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_CD) as (Par_BA_CD & Par_AB_DC & Par_BA_DC).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AB_CD) as Par_CD_AB.
	pose proof (by_prop_Par_flip _ _ _ _ Par_CD_AB) as (Par_DC_AB & Par_CD_BA & Par_DC_BA).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (nCol_A_B_C & nCol_A_C_D & nCol_B_C_D & nCol_A_B_D).

	pose proof (by_prop_nCol_order _ _ _ nCol_A_C_D) as (nCol_C_A_D & nCol_C_D_A & nCol_D_A_C & nCol_A_D_C & nCol_D_C_A).

	assert (Par_AB_CD_2 := Par_AB_CD).
	destruct Par_AB_CD_2 as (_ & _ & _ & _ & _ & neq_A_B & neq_C_D & _ & _ & _ & _ & _ & _ & n_Meet_A_B_C_D & _ & _).

	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_neq_symmetric _ _ neq_C_D) as neq_D_C.

	assert (Par_DC_AB_2 := Par_DC_AB).
	destruct Par_DC_AB_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_D_C_A_B & _ & _).

	pose proof (by_prop_Par_flip _ _ _ _ Par_AD_BC) as (Par_DA_BC & Par_AD_CB & Par_DA_CB).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AD_BC) as Par_BC_AD.
	pose proof (by_prop_Par_flip _ _ _ _ Par_BC_AD) as (Par_CB_AD & Par_BC_DA & Par_CB_DA).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AD_BC) as (nCol_A_D_B & _ & nCol_D_B_C &_ ).

	assert (Par_AD_BC_2 := Par_AD_BC).
	destruct Par_AD_BC_2 as (_ & _ & _ & _ & _ & neq_A_D & neq_B_C & _ & _ & _ & _ & _ & _ & n_Meet_A_D_B_C & _ & _).

	pose proof (by_prop_neq_symmetric _ _ neq_A_D) as neq_D_A.
	pose proof (by_prop_neq_symmetric _ _ neq_B_C) as neq_C_B.

	pose proof (by_prop_Par_flip _ _ _ _ Par_EB_CF) as (Par_BE_CF & Par_EB_FC & Par_BE_FC).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_EB_CF) as Par_CF_EB.
	pose proof (by_prop_Par_flip _ _ _ _ Par_CF_EB) as (Par_FC_EB & Par_CF_BE & Par_FC_BE).
	pose proof (by_prop_Par_NC _ _ _ _ Par_EB_CF) as (nCol_E_B_C & nCol_E_C_F & nCol_B_C_F & nCol_E_B_F).

	assert (Par_EB_CF_2 := Par_EB_CF).
	destruct Par_EB_CF_2 as (_ & _ & _ & _ & _ & neq_E_B & neq_C_F & _ & _ & _ & _ & _ & _ & n_Meet_E_B_C_F & _ & _).

	pose proof (by_prop_neq_symmetric _ _ neq_E_B) as neq_B_E.
	pose proof (by_prop_neq_symmetric _ _ neq_C_F) as neq_F_C.

	pose proof (by_prop_Par_flip _ _ _ _ Par_EF_BC) as (Par_FE_BC & Par_EF_CB & Par_FE_CB).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_EF_BC) as Par_BC_EF.
	pose proof (by_prop_Par_flip _ _ _ _ Par_BC_EF) as (Par_CB_EF & Par_BC_FE & Par_CB_FE).
	pose proof (by_prop_Par_NC _ _ _ _ Par_EF_BC) as (nCol_E_F_B & _ & nCol_F_B_C & nCol_E_F_C).

	assert (Par_EF_BC_2 := Par_EF_BC).
	destruct Par_EF_BC_2 as (_ & _ & _ & _ & _ & neq_E_F & _ & _ & _ & _ & _ & _ & _ & n_Meet_E_F_B_C & _ & _).

	pose proof (by_prop_neq_symmetric _ _ neq_E_F) as neq_F_E.

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AD_BC Cong_BC_EF) as Cong_AD_EF.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AD_EF) as (Cong_DA_FE & Cong_DA_EF & Cong_AD_FE).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AD_EF) as Cong_EF_AD.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_EF_AD) as (Cong_FE_DA & Cong_FE_AD & Cong_EF_DA).


	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_A_F Col_D_A_E neq_D_A) as Col_A_F_E.
	pose proof (by_prop_Col_order _ _ _ Col_A_F_E) as (Col_F_A_E & Col_F_E_A & Col_E_A_F & Col_A_E_F & Col_E_F_A).

	pose proof (by_def_Parallelogram _ _ _ _ Par_DC_BA Par_DA_CB) as Parallelogram_D_C_B_A.
	pose proof (by_def_Parallelogram _ _ _ _ Par_FC_BE Par_FE_CB) as Parallelogram_F_C_B_E.

	assert (BetS A D F \/ ~ BetS A D F) as [BetS_A_D_F|n_BetS_A_D_F] by (apply Classical_Prop.classic).
	{
		(* case BetS_A_D_F *)
		pose proof (proposition_35A _ _ _ _ _ _ Parallelogram_A_B_C_D Parallelogram_E_B_C_F BetS_A_D_F Col_A_E_F) as EqAreaQuad_ABCD_EBCF.

		exact EqAreaQuad_ABCD_EBCF.
	}
	(* case n_BetS_A_D_F *)
	assert (BetS E A D \/ ~ BetS E A D) as [BetS_E_A_D|n_BetS_E_A_D] by (apply Classical_Prop.classic).
	{
		(* case BetS_E_A_D *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_A_D) as BetS_D_A_E.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_E_A_D) as (_ & neq_E_A & neq_E_D).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_D_A_E) as (neq_A_E & _ & neq_D_E).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_D_E Col_A_D_F neq_A_D) as Col_D_E_F.
		pose proof (by_prop_Col_order _ _ _ Col_D_E_F) as (_ & _ & _ & Col_D_F_E & _).

		pose proof (proposition_35A _ _ _ _ _ _ Parallelogram_D_C_B_A Parallelogram_F_C_B_E BetS_D_A_E Col_D_F_E) as EqAreaQuad_DCBA_FCBE.

		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_DCBA_FCBE) as (_ & EqAreaQuad_DCBA_EBCF & _ & _ & _ & _ & _).
		pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_DCBA_EBCF) as EqAreaQuad_EBCF_DCBA.
		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_EBCF_DCBA) as (_ & EqAreaQuad_EBCF_ABCD & _ & _ & _ & _ & _).
		pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_EBCF_ABCD) as EqAreaQuad_ABCD_EBCF.

		exact EqAreaQuad_ABCD_EBCF.
	}
	(* case n_BetS_E_A_D *)

	assert (~ BetS A D E) as n_BetS_A_D_E.
	{
		intro BetS_A_D_E.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_E) as BetS_E_D_A.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_A_D_E) as (neq_D_E & _ & neq_A_E).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_E_D_A) as (_ & neq_E_D & neq_E_A).

		pose proof (lemma_parallelPasch _ _ _ _ _ Parallelogram_A_B_C_D BetS_A_D_E) as (H & BetS_B_H_E & BetS_C_H_D).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_H_E) as BetS_E_H_B.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_B_H_E) as (neq_H_E & neq_B_H &_ ).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_E_H_B) as (neq_H_B & neq_E_H &_ ).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_H_E) as Col_B_H_E.
		pose proof (by_prop_Col_order _ _ _ Col_B_H_E) as (Col_H_B_E & Col_H_E_B & Col_E_B_H & Col_B_E_H & Col_E_H_B).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_H_D) as BetS_D_H_C.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_C_H_D) as (neq_H_D & neq_C_H & _).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_D_H_C) as (neq_H_C & neq_D_H & _).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_H_D) as Col_C_H_D.
		pose proof (by_prop_Col_order _ _ _ Col_C_H_D) as (Col_H_C_D & Col_H_D_C & Col_D_C_H & Col_C_D_H & Col_D_H_C).


		pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_D_B Col_A_D_D Col_A_D_E neq_D_E) as nCol_D_E_B.
		pose proof (by_prop_nCol_order _ _ _ nCol_D_E_B) as (_ & _ & _ & _ & nCol_B_E_D).
		pose proof (by_def_n_Col_from_nCol _ _ _ nCol_B_E_D) as n_Col_B_E_D.

		pose proof (by_def_OppositeSide _ _ _ _ _ BetS_D_H_C Col_B_E_H nCol_B_E_D) as OppositeSide_D_BE_C.
		pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_D_BE_C) as OppositeSide_C_BE_D.

		pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_BE_FC) as TarskiPar_BE_FC.
		assert (TarskiPar_BE_FC_2 := TarskiPar_BE_FC).
		destruct TarskiPar_BE_FC_2 as (_ & _ & n_Meet_B_E_F_C & SameSide_F_C_BE).

		pose proof (lemma_planeseparation _ _ _ _ _ SameSide_F_C_BE OppositeSide_C_BE_D) as OppositeSide_F_BE_D.

		destruct OppositeSide_F_BE_D as (e & BetS_F_e_D & Col_B_E_e & nCol_B_E_F).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_e_D) as BetS_D_e_F.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_F_e_D) as (neq_e_D & neq_F_e & neq_F_D).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_D_e_F) as (neq_e_F & neq_D_e & neq_D_F).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_F_e_D) as Col_F_e_D.
		pose proof (by_prop_Col_order _ _ _ Col_F_e_D) as (Col_e_F_D & Col_e_D_F & Col_D_F_e & Col_F_D_e & Col_D_e_F).

		pose proof (by_prop_Col_order _ _ _ Col_B_E_e) as (Col_E_B_e & Col_E_e_B & Col_e_B_E & Col_B_e_E & Col_e_E_B).

		assert (~ neq e E) as n_neq_e_E.
		{
			intro neq_e_E.

			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_D_E Col_A_D_F neq_A_D) as Col_D_E_F.
			pose proof (by_prop_Col_order _ _ _ Col_D_E_F) as (_ & _ & Col_F_D_E & _ & _).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_F_D_E Col_F_D_e neq_F_D) as Col_D_E_e.
			pose proof (by_prop_Col_order _ _ _ Col_D_E_e) as (_ & _ & _ & _ & Col_e_E_D).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_e_E_D Col_e_E_B neq_e_E) as Col_E_D_B.
			pose proof (by_prop_Col_order _ _ _ Col_E_D_B) as (_ & _ & Col_B_E_D & _ & _).

			contradict Col_B_E_D.
			exact n_Col_B_E_D.
		}
		assert (eq_e_E := n_neq_e_E).
		apply Classical_Prop.NNPP in eq_e_E.


		assert (BetS F E D) as BetS_F_E_D by (rewrite <- eq_e_E; exact BetS_F_e_D).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_E_D) as BetS_D_E_F.
		pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_A_D_E BetS_D_E_F) as BetS_A_D_F.

		contradict BetS_A_D_F.
		exact n_BetS_A_D_F.
	}
	(* asserted n_BetS_A_D_E. *)

	assert (~ BetS D A F) as n_BetS_D_A_F.
	{
		intro BetS_D_A_F.

		pose proof (lemma_parallelPasch _ _ _ _ _ Parallelogram_D_C_B_A BetS_D_A_F) as (H & BetS_C_H_F & BetS_B_H_A).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_H_A) as BetS_A_H_B.

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_H_F) as Col_C_H_F.
		pose proof (by_prop_Col_order _ _ _ Col_C_H_F) as (_ & _ & _ & Col_C_F_H & _).

		pose proof (by_prop_BetS_notequal _ _ _ BetS_D_A_F) as (neq_A_F & _ & _).

		pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_D_A_C Col_D_A_A Col_D_A_F neq_A_F) as nCol_A_F_C.
		pose proof (by_prop_nCol_order _ _ _ nCol_A_F_C) as (nCol_F_A_C & nCol_F_C_A & nCol_C_A_F & nCol_A_C_F & nCol_C_F_A).

		pose proof (by_def_n_Col_from_nCol _ _ _ nCol_C_F_A) as n_Col_C_F_A.

		pose proof (by_def_OppositeSide _ _ _ _ _ BetS_A_H_B Col_C_F_H nCol_C_F_A) as OppositeSide_A_CF_B.
		pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_A_CF_B) as OppositeSide_B_CF_A.

		pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_CF_EB) as TarskiPar_CF_EB.
		assert (TarskiPar_CF_EB_2 := TarskiPar_CF_EB).
		destruct TarskiPar_CF_EB_2 as (_ & _ & n_Meet_C_F_E_B & SameSide_E_B_CF).

		pose proof (lemma_planeseparation _ _ _ _ _ SameSide_E_B_CF OppositeSide_B_CF_A) as OppositeSide_E_CF_A.

		destruct OppositeSide_E_CF_A as (e & BetS_E_e_A & Col_C_F_e & nCol_C_F_E).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_e_A) as BetS_A_e_E.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_E_e_A) as (neq_e_A & neq_E_e & neq_E_A).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_A_e_E) as (neq_e_E & neq_A_e & neq_A_E).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_e_A) as Col_E_e_A.
		pose proof (by_prop_Col_order _ _ _ Col_E_e_A) as (Col_e_E_A & Col_e_A_E & Col_A_E_e & Col_E_A_e & Col_A_e_E).

		pose proof (by_prop_Col_order _ _ _ Col_C_F_e) as (Col_F_C_e & Col_F_e_C & Col_e_C_F & Col_C_e_F & Col_e_F_C).

		assert (~ neq e F) as n_neq_e_F.
		{
			intro neq_e_F.

			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_E_A_F Col_E_A_e neq_E_A) as Col_A_F_e.
			pose proof (by_prop_Col_order _ _ _ Col_A_F_e) as (_ & _ & _ & _ & Col_e_F_A).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_e_F_A Col_e_F_C neq_e_F) as Col_F_A_C.
			pose proof (by_prop_Col_order _ _ _ Col_F_A_C) as (_ & _ & Col_C_F_A & _ & _).

			contradict Col_C_F_A.
			exact n_Col_C_F_A.
		}
		assert (eq_e_F := n_neq_e_F).
		apply Classical_Prop.NNPP in eq_e_F.


		assert (BetS E F A) as BetS_E_F_A by (rewrite <- eq_e_F; exact BetS_E_e_A).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_F_A) as BetS_A_F_E.
		pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_D_A_F BetS_A_F_E) as BetS_D_A_E.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_A_E) as BetS_E_A_D.

		contradict BetS_E_A_D.
		exact n_BetS_E_A_D.
	}
	(* asserted n_BetS_D_A_F. *)

	assert (~ eq A F) as n_eq_A_F.
	{
		intro eq_A_F.

		assert (Col F D E) as Col_F_D_E by (rewrite <-eq_A_F; exact Col_A_D_E).

		(* assert by cases *)
		assert (neq A F) as neq_A_F.
		destruct Col_F_D_E as [eq_F_D | [eq_F_E | [eq_D_E | [BetS_D_F_E | [BetS_F_D_E | BetS_F_E_D]]]]].
		{
			(* case eq_F_D *)
			assert (eq A D) as eq_A_D by (rewrite <- eq_F_D; exact eq_A_F).

			contradict eq_A_D.
			exact neq_A_D.
		}
		{
			(* case eq_F_E *)
			contradict eq_F_E.
			exact neq_F_E.
		}
		{
			(* case eq_D_E *)
			pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_E_B_C_F) as (p & BetS_E_p_C & BetS_B_p_F).

			pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_p_C) as Col_E_p_C.
			pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_p_F) as Col_B_p_F.
			pose proof (by_prop_Col_order _ _ _ Col_B_p_F) as (_ & _ & Col_F_B_p & _ & _).
			pose proof (by_prop_Col_order _ _ _ Col_E_p_C) as (_ & _ & _ & Col_E_C_p & _).
			pose proof (by_prop_nCol_distinct _ _ _ nCol_E_F_C) as (_ & _ & neq_E_C & _ & _ & _).
			pose proof (by_prop_nCol_distinct _ _ _ nCol_E_F_B) as (_ & neq_F_B & _ & _ & _ & _).

			pose proof (by_def_Meet _ _ _ _ _ neq_E_C neq_F_B Col_E_C_p Col_F_B_p) as Meet_E_C_F_B.
			assert (Meet D C F B) as Meet_D_C_F_B by (rewrite eq_D_E; exact Meet_E_C_F_B).
			assert (Meet D C A B) as Meet_D_C_A_B by (rewrite eq_A_F; exact Meet_D_C_F_B).

			contradict Meet_D_C_A_B.
			exact n_Meet_D_C_A_B.
		}
		{
			(* case BetS_D_A_E *)
			assert (BetS D A E) as BetS_D_A_E by (rewrite eq_A_F; exact BetS_D_F_E).
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_A_E) as BetS_E_A_D.

			contradict BetS_E_A_D.
			exact n_BetS_E_A_D.
		}
		{
			(* case BetS_A_D_E *)
			assert (BetS A D E) as BetS_A_D_E by (rewrite eq_A_F; exact BetS_F_D_E).

			contradict BetS_A_D_E.
			exact n_BetS_A_D_E.
		}
		{
			(* case BetS_A_E_D *)
			assert (BetS A E D) as BetS_A_E_D by (rewrite eq_A_F; exact BetS_F_E_D).

			assert (Cong F E A E) as Cong_FE_AE by (rewrite <- eq_A_F; exact Cong_AE_AE).
			pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_FE_AE) as Cong_AE_FE.
			pose proof (by_def_Lt _ _ _ _ _ BetS_A_E_D Cong_AE_FE) as Lt_FE_AD.
			pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_FE_AD Cong_AD_EF) as Lt_FE_EF.
			pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_FE_EF Cong_EF_FE) as Lt_FE_FE.

			pose proof (by_prop_Lt_asymmetric _ _ _ _ Lt_FE_FE) as n_Lt_FE_FE.

			contradict Lt_FE_FE.
			exact n_Lt_FE_FE.
		}
		contradict eq_A_F.
		exact neq_A_F.
	}
	assert (neq_A_F := n_eq_A_F).


	assert (eq D F \/ neq D F) as [eq_D_F|neq_D_F] by (apply Classical_Prop.classic).
	{
		(* case eq_D_F *)
		assert (eq A E \/ neq A E) as [eq_A_E|neq_A_E] by (apply Classical_Prop.classic).
		{
			(* case eq_A_E *)
			pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_A_B_C_D) as (M & BetS_A_M_C & BetS_B_M_D).

			pose proof (by_prop_EqAreaQuad_reflexive _ _ _ _ _ BetS_A_M_C BetS_B_M_D nCol_A_B_C) as EqAreaQuad_ABCD_ABCD.
			assert (EqAreaQuad A B C D E B C D) as EqAreaQuad_ABCD_EBCD by (rewrite <- eq_A_E; exact EqAreaQuad_ABCD_ABCD).
			assert (EqAreaQuad A B C D E B C F) as EqAreaQuad_ABCD_EBCF by (rewrite <- eq_D_F; exact EqAreaQuad_ABCD_EBCD).

			exact EqAreaQuad_ABCD_EBCF.
		}
		(* case neq_A_E *)
		(* This branch leads to a contradiction *)

		(* assert by cases *)
		assert (Col_A_F_E_2 := Col_A_F_E).
		destruct Col_A_F_E_2 as [eq_A_F | [eq_A_E | [eq_F_E | [BetS_F_A_E | [BetS_A_F_E | BetS_A_E_F]]]]].
		{
			(* case eq_A_F *)
			contradict eq_A_F.
			exact neq_A_F.
		}
		{
			(* case eq_A_E *)
			contradict eq_A_E.
			exact neq_A_E.
		}
		{
			(* case eq_F_E *)
			contradict eq_F_E.
			exact neq_F_E.
		}
		{
			(* case BetS_D_A_E *)
			assert (BetS D A E) as BetS_D_A_E by (rewrite eq_D_F; exact BetS_F_A_E).
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_A_E) as BetS_E_A_D.

			contradict BetS_E_A_D.
			exact n_BetS_E_A_D.
		}
		{
			(* case BetS_A_D_E *)
			assert (BetS A D E) as BetS_A_D_E by (rewrite eq_D_F; exact BetS_A_F_E).

			contradict BetS_A_D_E.
			exact n_BetS_A_D_E.
		}
		{
			(* case BetS_A_E_D *)
			assert (BetS A E D) as BetS_A_E_D by (rewrite eq_D_F; exact BetS_A_E_F).

			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_D) as BetS_D_E_A.
			pose proof (by_def_Lt _ _ _ _ _ BetS_D_E_A Cong_DE_DE) as Lt_DE_DA.
			assert (Cong D E F E) as Cong_DE_FE by (rewrite <- eq_D_F; exact Cong_DE_DE).
			pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_DE_DA Cong_DE_FE) as Lt_FE_DA.
			pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_FE_DA Cong_FE_EF) as Lt_EF_DA.
			pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_EF_DA Cong_DA_AD) as Lt_EF_AD.
			pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_EF_AD Cong_AD_EF) as Lt_EF_EF.
			pose proof (by_prop_Lt_asymmetric _ _ _ _ Lt_EF_EF) as n_Lt_EF_EF.

			contradict Lt_EF_EF.
			exact n_Lt_EF_EF.
		}
	}
	(* case neq_D_F *)
	(* This branch leads to a contradiction *)

	(* assert by cases *)
	assert (Col_A_D_F_2 := Col_A_D_F).
	destruct Col_A_D_F_2 as [eq_A_D | [eq_A_F | [eq_D_F | [BetS_D_A_F | [BetS_A_D_F | BetS_A_F_D]]]]].
	{
		(* case eq_A_D *)
		contradict eq_A_D.
		exact neq_A_D.
	}
	{
		(* case eq_A_F *)
		contradict eq_A_F.
		exact neq_A_F.
	}
	{
		(* case eq_D_F *)
		contradict eq_D_F.
		exact neq_D_F.
	}
	{
		(* case BetS_D_A_F *)
		contradict BetS_D_A_F.
		exact n_BetS_D_A_F.
	}
	{
		(* case BetS_A_D_F *)
		contradict BetS_A_D_F.
		exact n_BetS_A_D_F.
	}
	(* case BetS_A_F_D *)
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_F_D) as BetS_D_F_A.

	(* assert by cases *)
	assert (Col_A_D_E_2 := Col_A_D_E).
	destruct Col_A_D_E_2 as [eq_A_D | [eq_A_E | [eq_D_E | [BetS_D_A_E | [BetS_A_D_E | BetS_A_E_D]]]]].
	{
		(* case eq_A_D *)
		contradict eq_A_D.
		exact neq_A_D.
	}
	{
		(* case eq_A_E *)
		assert (Cong A F E F) as Cong_AF_EF by (rewrite <- eq_A_E; exact Cong_AF_AF).
		pose proof (by_def_Lt _ _ _ _ _ BetS_A_F_D Cong_AF_EF) as Lt_EF_AD.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_EF_AD Cong_AD_EF) as Lt_EF_EF.
		pose proof (by_prop_Lt_asymmetric _ _ _ _ Lt_EF_EF) as n_Lt_EF_EF.

		contradict Lt_EF_EF.
		exact n_Lt_EF_EF.
	}
	{
		(* case eq_D_E *)
		pose proof (by_def_Lt _ _ _ _ _ BetS_D_F_A Cong_DF_DF) as Lt_DF_DA.
		assert (Lt E F D A) as Lt_EF_DA by (rewrite <- eq_D_E; exact Lt_DF_DA).
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_EF_DA Cong_DA_EF) as Lt_EF_EF.
		pose proof (by_prop_Lt_asymmetric _ _ _ _ Lt_EF_EF) as n_Lt_EF_EF.

		contradict Lt_EF_EF.
		exact n_Lt_EF_EF.
	}
	{
		(* case BetS_D_A_E *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_A_E) as BetS_E_A_D.

		contradict BetS_E_A_D.
		exact n_BetS_E_A_D.
	}
	{
		(* case BetS_A_D_E *)
		contradict BetS_A_D_E.
		exact n_BetS_A_D_E.
	}
	(* case BetS_A_E_D *)
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_D) as BetS_D_E_A.

	assert (~ BetS A E F) as n_BetS_A_E_F.
	{
		intro BetS_A_E_F.

		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_E_F BetS_A_F_D) as BetS_E_F_D.

		pose proof (by_def_Lt _ _ _ _ _ BetS_E_F_D Cong_EF_EF) as Lt_EF_ED.
		pose proof (by_def_Lt _ _ _ _ _ BetS_D_E_A Cong_DE_DE) as Lt_DE_DA.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_EF_ED Cong_ED_DE) as Lt_EF_DE.
		pose proof (by_prop_Lt_transitive _ _ _ _ _ _ Lt_EF_DE Lt_DE_DA) as Lt_EF_DA.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_EF_DA Cong_DA_AD) as Lt_EF_AD.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_EF_AD Cong_AD_EF) as Lt_EF_EF.
		pose proof (by_prop_Lt_asymmetric _ _ _ _ Lt_EF_EF) as n_Lt_EF_EF.

		contradict Lt_EF_EF.
		exact n_Lt_EF_EF.
	}

	assert (~ BetS A F E) as n_BetS_A_F_E.
	{
		intro BetS_A_F_E.

		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_F_E BetS_A_E_D) as BetS_F_E_D.

		pose proof (by_def_Lt _ _ _ _ _ BetS_F_E_D Cong_FE_FE) as Lt_FE_FD.
		pose proof (by_def_Lt _ _ _ _ _ BetS_D_F_A Cong_DF_DF) as Lt_DF_DA.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_FE_FD Cong_FD_DF) as Lt_FE_DF.
		pose proof (by_prop_Lt_transitive _ _ _ _ _ _ Lt_FE_DF Lt_DF_DA) as Lt_FE_DA.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_FE_DA Cong_DA_AD) as Lt_FE_AD.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_FE_AD Cong_AD_FE) as Lt_FE_FE.
		pose proof (by_prop_Lt_asymmetric _ _ _ _ Lt_FE_FE) as n_Lt_FE_FE.

		contradict Lt_FE_FE.
		exact n_Lt_FE_FE.
	}

	pose proof (axiom_connectivity _ _ _ _ BetS_A_E_D BetS_A_F_D n_BetS_A_E_F n_BetS_A_F_E) as eq_E_F.

	contradict eq_E_F.
	exact neq_E_F.
Qed.

End Euclid.
