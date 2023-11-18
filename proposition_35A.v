Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_CongTriangles.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B .
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col .
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_EqAreaQuad_reflexive.
Require Import ProofCheckingEuclid.by_prop_EqAreaTri_reflexive.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_OnRay_assert.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_flip.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_rotate.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_symmetric.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct .
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_35helper.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_diagonalsmeet.
Require Import ProofCheckingEuclid.lemma_differenceofparts.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_trapezoiddiagonals.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_29C.
Require Import ProofCheckingEuclid.proposition_34.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_35A :
	forall A B C D E F,
	Parallelogram A B C D ->
	Parallelogram E B C F ->
	BetS A D F ->
	Col A E F ->
	EqAreaQuad A B C D E B C F.
Proof.
	intros A B C D E F.
	intros Parallelogram_A_B_C_D.
	intros Parallelogram_E_B_C_F.
	intros BetS_A_D_F.
	intros Col_A_E_F.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq D D) as eq_D_D by (reflexivity).

	pose proof (by_def_Col_from_eq_A_C A D A eq_A_A) as Col_A_D_A.
	pose proof (by_def_Col_from_eq_A_C B C B eq_B_B) as Col_B_C_B.
	pose proof (by_def_Col_from_eq_B_C E A A eq_A_A) as Col_E_A_A.
	pose proof (by_def_Col_from_eq_B_C E D D eq_D_D) as Col_E_D_D.

	pose proof (cn_congruencereflexive A D) as Cong_AD_AD.
	pose proof (cn_congruencereverse A F) as Cong_AF_FA.
	pose proof (cn_congruencereverse D E) as Cong_DE_ED.
	pose proof (cn_congruencereverse E F) as Cong_EF_FE.

	assert (Parallelogram_A_B_C_D_2 := Parallelogram_A_B_C_D).
	destruct Parallelogram_A_B_C_D_2 as (Par_AB_CD & Par_AD_BC).

	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_CD) as (Par_BA_CD & Par_AB_DC & Par_BA_DC).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AB_CD) as Par_CD_AB.
	pose proof (by_prop_Par_flip _ _ _ _ Par_CD_AB) as (Par_DC_AB & Par_CD_BA & Par_DC_BA).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (nCol_A_B_C & nCol_A_C_D & nCol_B_C_D & nCol_A_B_D).

	assert (Par_AB_CD_2 := Par_AB_CD).
	destruct Par_AB_CD_2 as (_ & _ & _ & _ & _ & neq_A_B & neq_C_D & _ & _ & _ & _ & _ & _ & n_Meet_A_B_C_D & _ & _).

	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_neq_symmetric _ _ neq_C_D) as neq_D_C.

	pose proof (by_prop_Par_flip _ _ _ _ Par_AD_BC) as (Par_DA_BC & Par_AD_CB & Par_DA_CB).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AD_BC) as Par_BC_AD.
	pose proof (by_prop_Par_flip _ _ _ _ Par_BC_AD) as (Par_CB_AD & Par_BC_DA & Par_CB_DA).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AD_BC) as (nCol_A_D_B & _ & nCol_D_B_C & nCol_A_D_C).

	assert (Par_AD_BC_2 := Par_AD_BC).
	destruct Par_AD_BC_2 as (_ & _ & _ & _ & _ & neq_A_D & neq_B_C & _ & _ & _ & _ & _ & _ & n_Meet_A_D_B_C & _ & _).

	pose proof (by_prop_neq_symmetric _ _ neq_A_D) as neq_D_A.
	pose proof (by_prop_neq_symmetric _ _ neq_B_C) as neq_C_B.

	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_D) as (nCol_B_A_D & nCol_B_D_A & nCol_D_A_B & _ & nCol_D_B_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_D) as (_ & neq_B_D & _ & _ & neq_D_B &_ ).

	pose proof (by_prop_CongA_reflexive _ _ _ nCol_D_A_B) as CongA_DAB_DAB.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_F) as BetS_F_D_A.

	pose proof (proposition_34 _ _ _ _ Parallelogram_A_B_C_D) as (Cong_AD_BC & Cong_AB_DC & CongA_BAD_DCB & CongA_ADC_CBA & CongTriangles_BAD_DCB).
	pose proof (proposition_34 _ _ _ _ Parallelogram_E_B_C_F) as (Cong_EF_BC & Cong_EB_FC & CongA_BEF_FCB & CongA_EFC_CBE & CongTriangles_BEF_FCB).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AB_DC) as Cong_DC_AB.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_EF_BC) as Cong_BC_EF.

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AD_BC Cong_BC_EF) as Cong_AD_EF.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AD_EF Cong_EF_FE) as Cong_AD_FE.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AD_FE) as (Cong_DA_EF & _ & _).

	pose proof (by_prop_Parallelogram_symmetric _ _ _ _ Parallelogram_A_B_C_D) as Parallelogram_C_D_A_B.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_A_B_C_D) as Parallelogram_B_C_D_A.
	pose proof (by_prop_Parallelogram_symmetric _ _ _ _ Parallelogram_B_C_D_A) as Parallelogram_D_A_B_C.
	pose proof (by_prop_Parallelogram_flip _ _ _ _ Parallelogram_D_A_B_C) as Parallelogram_A_D_C_B.

	pose proof (by_prop_Parallelogram_flip _ _ _ _ Parallelogram_E_B_C_F) as Parallelogram_B_E_F_C.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_E_B_C_F) as Parallelogram_B_C_F_E.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_B_C_F_E) as Parallelogram_C_F_E_B.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_C_F_E_B) as Parallelogram_F_E_B_C.

	pose proof (lemma_35helper _ _ _ _ _ _ Parallelogram_A_B_C_D Parallelogram_E_B_C_F BetS_A_D_F Col_A_E_F) as BetS_A_E_F.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_F) as BetS_F_E_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_E_F) as (neq_E_F & neq_A_E & neq_A_F).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_F_E_A) as (neq_E_A & neq_F_E & neq_F_A).

	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_AD_BC) as TarskiPar_AD_BC.
	assert (TarskiPar_AD_BC_2 := TarskiPar_AD_BC).
	destruct TarskiPar_AD_BC_2 as (_ & _ & _ & SameSide_B_C_AD).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_B_C_AD) as (_ & _ & SameSide_C_B_DA).
	pose proof (proposition_29C _ _ _ _ _ Par_DC_AB SameSide_C_B_DA BetS_F_D_A) as (CongA_FDC_DAB & _).

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_A_B) as OnRay_AB_B.

	assert (~ ~ (BetS A D E \/ eq D E \/ BetS A E D)) as n_n_BetS_A_D_E_or_eq_D_E_or_BetS_A_E_D.
	{
		intro n_BetS_A_D_E_or_eq_D_E_or_BetS_A_E_D.

		apply Classical_Prop.not_or_and in n_BetS_A_D_E_or_eq_D_E_or_BetS_A_E_D.
		destruct n_BetS_A_D_E_or_eq_D_E_or_BetS_A_E_D as (n_BetS_A_D_E & eq_D_E_or_n_BetS_A_E_D).
		apply Classical_Prop.not_or_and in eq_D_E_or_n_BetS_A_E_D.
		destruct eq_D_E_or_n_BetS_A_E_D as (neq_D_E & n_BetS_A_E_D).

		pose proof (axiom_connectivity _ _ _ _ BetS_A_D_F BetS_A_E_F n_BetS_A_D_E n_BetS_A_E_D) as eq_D_E.

		contradict eq_D_E.
		exact neq_D_E.
	}
	assert (BetS_A_D_E_or_eq_D_E_or_BetS_A_E_D := n_n_BetS_A_D_E_or_eq_D_E_or_BetS_A_E_D).
	apply Classical_Prop.NNPP in BetS_A_D_E_or_eq_D_E_or_BetS_A_E_D.

	pose proof (by_prop_OnRay_assert A E D BetS_A_D_E_or_eq_D_E_or_BetS_A_E_D neq_A_E) as OnRay_AE_D.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_AE_D) as OnRay_AD_E.

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_DAB_DAB OnRay_AD_E OnRay_AB_B) as CongA_DAB_EAB.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_FDC_DAB CongA_DAB_EAB) as CongA_FDC_EAB.


	(* assert by cases *)
	assert (Cong A E D F) as Cong_AE_DF.
	destruct BetS_A_D_E_or_eq_D_E_or_BetS_A_E_D as [BetS_A_D_E | [eq_D_E | BetS_A_E_D ] ].
	{
		(* case BetS_A_D_E *)
		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_D_E BetS_A_E_F) as BetS_D_E_F.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_E_F) as BetS_F_E_D.
		pose proof (cn_sumofparts _ _ _ _ _ _ Cong_AD_FE Cong_DE_ED BetS_A_D_E BetS_F_E_D) as Cong_AE_FD.
		pose proof (by_prop_Cong_flip _ _ _ _ Cong_AE_FD) as (_ & _ & Cong_AE_DF).

		exact Cong_AE_DF.
	}
	{
		(* case eq_D_E *)
		assert (Cong A E E F) as Cong_AE_EF by (setoid_rewrite <-eq_D_E at 1; exact Cong_AD_EF).
		assert (Cong A E D F) as Cong_AE_DF by (rewrite eq_D_E; exact Cong_AE_EF).

		exact Cong_AE_DF.
	}
	{
		(* case BetS_A_E_D *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_D) as BetS_D_E_A.
		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_E_D BetS_A_D_F) as BetS_E_D_F.
		pose proof (lemma_differenceofparts _ _ _ _ _ _ Cong_DE_ED Cong_DA_EF BetS_D_E_A BetS_E_D_F) as Cong_EA_DF.
		pose proof (by_prop_Cong_flip _ _ _ _ Cong_EA_DF) as (_ & Cong_AE_DF & _).

		exact Cong_AE_DF.
	}
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AE_DF) as Cong_DF_AE.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_DF_AE) as (Cong_FD_EA & _ & _).

	pose proof (proposition_04 _ _ _ _ _ _ Cong_DF_AE Cong_DC_AB CongA_FDC_EAB) as (Cong_FC_EB & CongA_DFC_AEB & CongA_DCF_ABE).

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_DCF_ABE) as CongA_ABE_DCF.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_ABE_DCF) as nCol_D_C_F.
	pose proof (by_prop_nCol_order _ _ _ nCol_D_C_F) as (nCol_C_D_F & _ & _ & _ & _).

	pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_FD_EA Cong_DC_AB Cong_FC_EB) as CongTriangles_FDC_EAB.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_FDC_EAB) as EqAreaTri_FDC_EAB.

	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_FDC_EAB) as EqAreaTri_EAB_FDC.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_FDC_EAB) as (_ & _ & EqAreaTri_FDC_AEB & _ &  EqAreaTri_FDC_BEA).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_FDC_AEB) as EqAreaTri_AEB_FDC.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_EAB_FDC) as (_ & _ & EqAreaTri_EAB_DFC & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_FDC_BEA) as EqAreaTri_BEA_FDC.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_BEA_FDC) as (_ & _ & _ & EqAreaTri_BEA_CDF & _).

	(* assert by cases *)
	assert (EqAreaQuad A B C D E B C F) as EqAreaQuad_ABCD_EBCF.
	destruct BetS_A_D_E_or_eq_D_E_or_BetS_A_E_D as [BetS_A_D_E | [eq_D_E | BetS_A_E_D ] ].
	{
		(* case BetS_A_D_E *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_E) as BetS_E_D_A.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_A_D_E) as (neq_D_E & _ &_ ).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_E_D_A) as (_ & neq_E_D &_ ).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_D_E) as Col_A_D_E.
		pose proof (by_prop_Col_order _ _ _ Col_A_D_E) as (Col_D_A_E & Col_D_E_A & Col_E_A_D & Col_A_E_D & Col_E_D_A).

		pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_A_B_C_D) as (M & BetS_A_M_C & BetS_B_M_D).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_M_C) as BetS_C_M_A.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_A_M_C) as (neq_M_C & neq_A_M & neq_A_C).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_C_M_A) as (neq_M_A & neq_C_M & neq_C_A).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_M_C) as Col_A_M_C.
		pose proof (by_prop_Col_order _ _ _ Col_A_M_C) as (Col_M_A_C & Col_M_C_A & Col_C_A_M & Col_A_C_M & Col_C_M_A).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_D) as BetS_D_M_B.

		pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_D_B Col_A_D_A Col_A_D_E neq_A_E) as nCol_A_E_B.
		pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_D_C Col_A_D_A Col_A_D_E neq_A_E) as nCol_A_E_C.
		pose proof (by_prop_nCol_order _ _ _ nCol_A_E_C) as (_ & _ & nCol_C_A_E & _ & _).

		pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_B_M_D BetS_A_D_E nCol_A_E_B) as (H & BetS_B_H_E & BetS_A_M_H).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_H_E) as BetS_E_H_B.

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_M_H) as Col_A_M_H.
		pose proof (by_prop_Col_order _ _ _ Col_A_M_H) as (Col_M_A_H & _ & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_M_A_H Col_M_A_C neq_M_A) as Col_A_H_C.
		pose proof (by_prop_Col_order _ _ _ Col_A_H_C) as (_ & _ & _ & Col_A_C_H & _).

		assert (~ Meet E A C B) as n_Meet_E_A_C_B.
		{
			intro Meet_E_A_C_B.

			destruct Meet_E_A_C_B as (q & _ & _ & Col_E_A_q & Col_C_B_q).

			pose proof (by_prop_Col_order _ _ _ Col_C_B_q) as (Col_B_C_q & _ & _ & _ & _).
			pose proof (by_prop_Col_order _ _ _ Col_E_A_q) as (Col_A_E_q & _ & _ & _ & _).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_E_A_D Col_E_A_q neq_E_A) as Col_A_D_q.

			pose proof (by_def_Meet _ _ _ _ _ neq_A_D neq_B_C Col_A_D_q Col_B_C_q) as Meet_A_D_B_C.

			contradict Meet_A_D_B_C.
			exact n_Meet_A_D_B_C.
		}

		pose proof (by_def_Col_from_eq_A_B C C B eq_C_C) as Col_C_C_B.

		pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_E_A_A Col_C_C_B neq_E_A neq_C_B neq_E_A neq_C_B n_Meet_E_A_C_B BetS_E_H_B Col_A_C_H) as BetS_A_H_C.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_H_C) as BetS_C_H_A.

		pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_C_H_A BetS_E_D_A nCol_C_A_E) as (G & BetS_C_G_D & BetS_E_G_H).

		assert (eq G G) as eq_G_G by (reflexivity).
		pose proof (by_def_Col_from_eq_B_C E G G eq_G_G) as Col_E_G_G.
		pose proof (by_def_Col_from_eq_B_C D G G eq_G_G) as Col_D_G_G.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_G_D) as BetS_D_G_C.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_C_G_D) as (neq_G_D & neq_C_G & _).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_D_G_C) as (neq_G_C & neq_D_G & _).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_G_D) as Col_C_G_D.
		pose proof (by_prop_Col_order _ _ _ Col_C_G_D) as (Col_G_C_D & Col_G_D_C & Col_D_C_G & Col_C_D_G & Col_D_G_C).

		pose proof (by_prop_BetS_notequal _ _ _ BetS_E_G_H) as (_ & neq_E_G & _).
		pose proof (by_prop_neq_symmetric _ _ neq_E_G) as neq_G_E.

		pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_E_G_H BetS_E_H_B) as BetS_E_G_B.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_G_B) as BetS_B_G_E.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_E_G_B) as (neq_G_B & _ & neq_E_B).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_B_G_E) as (_ & neq_B_G & neq_B_E).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_G_B) as Col_E_G_B.
		pose proof (by_prop_Col_order _ _ _ Col_E_G_B) as (Col_G_E_B & Col_G_B_E & Col_B_E_G & Col_E_B_G & Col_B_G_E).

		assert (~ Col D E G) as n_Col_D_E_G.
		{
			intro Col_D_E_G.

			pose proof (by_prop_Col_order _ _ _ Col_D_E_G) as (_ & _ & _ & _ & Col_G_E_D).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_G_E_D Col_G_E_B neq_G_E) as Col_E_D_B.
			pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_E_D Col_E_D_A Col_E_D_D Col_E_D_B) as Col_A_D_B.

			pose proof (by_def_Meet _ _ _ _ _ neq_A_D neq_B_C Col_A_D_B Col_B_C_B) as Meet_A_D_B_C.

			contradict Meet_A_D_B_C.
			exact n_Meet_A_D_B_C.
		}
		pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_D_E_G) as nCol_D_E_G.

		pose proof (by_prop_nCol_order _ _ _ nCol_D_E_G) as (_ & nCol_E_G_D & _ & _ & _).
		pose proof (by_def_Triangle _ _ _ nCol_D_E_G) as Triangle_DEG.
		pose proof (by_prop_EqAreaTri_reflexive _ _ _ Triangle_DEG) as EqAreaTri_DEG_DEG.

		pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_DEG_DEG) as (_ & _ & EqAreaTri_DEG_EDG & _ & _).

		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_D_E BetS_A_E_F) as BetS_D_E_F.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_E_F) as BetS_F_E_D.

		(*
			area(△AEB) = area(△FDC) ->
			area(△AEB) - area(△DEG) = area(△FDC) - area(△DEG)
		*)
		pose proof (
			axiom_cutoff1
			A D E G B
			F E D G C
			BetS_A_D_E BetS_F_E_D
			BetS_B_G_E BetS_C_G_D
			EqAreaTri_DEG_EDG
			EqAreaTri_AEB_FDC
		) as EqAreaQuad_ADGB_FEGC.

		pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_E_G_D Col_E_G_B Col_E_G_G neq_B_G) as nCol_B_G_D.
		pose proof (by_prop_nCol_order _ _ _ nCol_B_G_D) as (_ & _ & _ & _ & nCol_D_G_B).
		pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_D_G_B Col_D_G_C Col_D_G_G neq_C_G) as nCol_C_G_B.
		pose proof (by_prop_nCol_order _ _ _ nCol_C_G_B) as (nCol_G_C_B & _ & _ & _ & _).

		pose proof (by_def_Triangle _ _ _ nCol_G_C_B) as Triangle_GCB.
		pose proof (by_prop_EqAreaTri_reflexive _ _ _ Triangle_GCB) as EqAreaTri_GCB_GCB.
		pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_GCB_GCB) as (_ & EqAreaTri_GCB_GBC & _ & _ & _).

		pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_A_D_C_B) as (q & BetS_A_q_C & BetS_D_q_B).
		pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_F_E_B_C) as (m & BetS_F_m_B & BetS_E_m_C).

		(*
			area(ADGB) = area(FEGC) ->
			area(ADGB) + area(△BCG) = area(FEGC) + area(△BCG)
		*)
		pose proof (
			axiom_paste2
			_ _ _ _ _ _ _ _ _ _ _ _
			BetS_D_G_C BetS_E_G_B
			EqAreaTri_GCB_GBC EqAreaQuad_ADGB_FEGC
			BetS_A_M_C BetS_D_M_B
			BetS_F_m_B BetS_E_m_C
		) as EqAreaQuad_ADCB_FEBC.

		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_ADCB_FEBC) as (EqAreaQuad_ADCB_EBCF & _ & _ & _ & _ & _ & _).
		pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_ADCB_EBCF) as EqAreaQuad_EBCF_ADCB.
		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_EBCF_ADCB) as (_ & _ & _ & _ & _ & _ & EqAreaQuad_EBCF_ABCD).
		pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_EBCF_ABCD) as EqAreaQuad_ABCD_EBCF.

		exact EqAreaQuad_ABCD_EBCF.
	}
	{
		(* case eq_D_E *)
		assert (nCol E B C) as nCol_E_B_C by (rewrite <- eq_D_E; exact nCol_D_B_C).
		pose proof (by_prop_nCol_order _ _ _ nCol_E_B_C) as (nCol_B_E_C & _ & _ & _ & _).
		pose proof (by_def_Triangle _ _ _ nCol_B_E_C) as Triangle_BEC.
		pose proof (by_prop_EqAreaTri_reflexive _ _ _ Triangle_BEC) as EqAreaTri_BEC_BEC.
		pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_BEC_BEC) as (_ & _ & _ & EqAreaTri_BEC_CEB & _).
		assert (EqAreaTri B E C C D B) as EqAreaTri_BEC_CDB by (rewrite eq_D_E; exact EqAreaTri_BEC_CEB).

		pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_A_B_C_D) as (J & BetS_A_J_C & BetS_B_J_D).
		assert (BetS B J E) as BetS_B_J_E by (rewrite <- eq_D_E; exact BetS_B_J_D).

		pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_E_B_C_F) as (j & BetS_E_j_C & BetS_B_j_F).
		assert (BetS D j C) as BetS_D_j_C by (rewrite eq_D_E; exact BetS_E_j_C).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_j_C) as BetS_C_j_D.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_j_F) as BetS_F_j_B.

		assert (BetS B J E \/ eq B J \/ eq J E) as BetS_B_J_E' by (left; exact BetS_B_J_E).
		assert (BetS C j D \/ eq C j \/ eq j D) as BetS_C_j_D' by (left; exact BetS_C_j_D).

		pose proof (
			axiom_paste3
			B E A C J C D F B j
			EqAreaTri_BEA_CDF
			EqAreaTri_BEC_CDB
			BetS_A_J_C
			BetS_B_J_E'
			BetS_F_j_B
			BetS_C_j_D'
		) as EqAreaQuad_BAEC_CFDB.

		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_BAEC_CFDB) as (_ & _ & EqAreaQuad_BAEC_DBCF & _ & _ & _ & _).
		assert (EqAreaQuad B A E C E B C F) as EqAreaQuad_BAEC_EBCF by (setoid_rewrite <-eq_D_E at 2; exact EqAreaQuad_BAEC_DBCF ).
		pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_BAEC_EBCF) as EqAreaQuad_EBCF_BAEC.
		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_EBCF_BAEC) as (_ & _ & _ & EqAreaQuad_EBCF_ABCE & _ & _ & _).
		assert (EqAreaQuad E B C F A B C D) as EqAreaQuad_EBCF_ABCD by (rewrite eq_D_E; exact EqAreaQuad_EBCF_ABCE).
		pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_EBCF_ABCD) as EqAreaQuad_ABCD_EBCF.

		exact EqAreaQuad_ABCD_EBCF.
	}
	{
		(* case BetS_A_E_D *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_D) as BetS_D_E_A.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_A_E_D) as (neq_E_D & _ & _).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_E_D) as Col_A_E_D.
		pose proof (by_prop_Col_order _ _ _ Col_A_E_D) as (Col_E_A_D & Col_E_D_A & Col_D_A_E & Col_A_D_E & Col_D_E_A).

		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_E_D BetS_A_D_F) as BetS_E_D_F.

		pose proof (lemma_trapezoiddiagonals _ _ _ _ _ Parallelogram_A_B_C_D BetS_A_E_D) as (H & BetS_B_H_D & BetS_C_H_E).
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_H_E) as BetS_E_H_C.

		assert (~ Col B E D) as n_Col_B_E_D.
		{
			intro Col_B_E_D.

			pose proof (by_prop_Col_order _ _ _ Col_B_E_D) as (_ & Col_E_D_B & _ & _ & _).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_E_D_A Col_E_D_B neq_E_D) as Col_D_A_B.
			pose proof (by_prop_Col_order _ _ _ Col_D_A_B) as (Col_A_D_B & _ & _ & _ & _).
			pose proof (by_def_Meet _ _ _ _ _ neq_A_D neq_B_C Col_A_D_B Col_B_C_B) as Meet_A_D_B_C.

			contradict Meet_A_D_B_C.
			exact n_Meet_A_D_B_C.
		}
		pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_B_E_D) as nCol_B_E_D.

		pose proof (by_prop_EqAreaQuad_reflexive _ _ _ _ _ BetS_B_H_D BetS_E_H_C nCol_B_E_D) as EqAreaQuad_BEDC_BEDC.
		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_BEDC_BEDC) as (_ & EqAreaQuad_BEDC_CDEB & _ & _ & _ & _ & _).
		pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_BEDC_CDEB) as EqAreaQuad_CDEB_BEDC.

		pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_C_D_A_B) as (p & BetS_C_p_A & BetS_D_p_B).
		pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_B_E_F_C) as (m & BetS_B_m_F & BetS_E_m_C).

		(*
			area(△ABE) = area(△CDF) ->
			area(BCDE) + area(△ABE) = area(BCDE) + area(△CDF)
		*)
		pose proof (
			axiom_paste2
			_ _ _ _ _ _ _ _ _ _ _ _
			BetS_D_E_A BetS_E_D_F
			EqAreaTri_EAB_DFC EqAreaQuad_CDEB_BEDC
			BetS_C_p_A BetS_D_p_B
			BetS_B_m_F BetS_E_m_C
		) as EqAreaQuad_CDAB_BEFC.

		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_CDAB_BEFC) as (_ & _ & _ & EqAreaQuad_CDAB_EBCF & _ & _ & _).
		pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_CDAB_EBCF) as EqAreaQuad_EBCF_CDAB.
		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_EBCF_CDAB) as (_ & _ & EqAreaQuad_EBCF_ABCD & _ & _ & _ & _).
		pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_EBCF_ABCD) as EqAreaQuad_ABCD_EBCF.

		exact EqAreaQuad_ABCD_EBCF.
	}
	exact EqAreaQuad_ABCD_EBCF.
Qed.

End Euclid.
