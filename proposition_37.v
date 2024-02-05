Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_rotate.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_diagonalsmeet.
Require Import ProofCheckingEuclid.lemma_triangletoparallelogram.
Require Import ProofCheckingEuclid.proposition_34.
Require Import ProofCheckingEuclid.proposition_35.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_37 :
	forall A B C D,
	Par A D B C ->
	EqAreaTri A B C D B C.
Proof.
	intros A B C D.
	intros Par_AD_BC.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq D D) as eq_D_D by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C A D A eq_A_A) as Col_A_D_A.
	pose proof (by_def_Col_from_eq_B_C A D D eq_D_D) as Col_A_D_D.

	pose proof (by_prop_Par_flip _ _ _ _ Par_AD_BC) as (Par_DA_BC & Par_AD_CB & Par_DA_CB).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AD_BC) as Par_BC_AD.
	pose proof (by_prop_Par_flip _ _ _ _ Par_BC_AD) as (Par_CB_AD & Par_BC_DA & Par_CB_DA).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AD_BC) as (nCol_A_D_B & nCol_A_B_C & nCol_D_B_C & nCol_A_D_C).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_D_B) as (neq_A_D & neq_D_B & neq_A_B & neq_D_A & neq_B_D & neq_B_A).

	pose proof (lemma_triangletoparallelogram _ _ _ _ _ Par_CB_AD Col_A_D_A) as (E & Parallelogram_A_E_B_C & Col_A_D_E).
	pose proof (lemma_triangletoparallelogram _ _ _ _ _ Par_CB_AD Col_A_D_D) as (F & Parallelogram_D_F_B_C & Col_A_D_F).

	pose proof (by_prop_Col_order _ _ _ Col_A_D_E) as (Col_D_A_E & Col_D_E_A & Col_E_A_D & Col_A_E_D & Col_E_D_A).
	pose proof (by_prop_Col_order _ _ _ Col_A_D_F) as (Col_D_A_F & Col_D_F_A & Col_F_A_D & Col_A_F_D & Col_F_D_A).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_A_F Col_D_A_E neq_D_A) as Col_A_F_E.
	pose proof (by_prop_Col_order _ _ _ Col_A_F_E) as (_ & _ & Col_E_A_F & _ & _).

	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_A_E_B_C) as Parallelogram_E_B_C_A.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_D_F_B_C) as Parallelogram_F_B_C_D.

	assert (Parallelogram_E_B_C_A_2 := Parallelogram_E_B_C_A).
	destruct Parallelogram_E_B_C_A_2 as (Par_EB_CA & Par_EA_BC).

	pose proof (by_prop_Par_NC _ _ _ _ Par_EB_CA) as (_ & _ & _ & nCol_E_B_A).
	pose proof (by_prop_nCol_order _ _ _ nCol_E_B_A) as (_ & nCol_B_A_E & _ & _ & _).

	assert (Parallelogram_D_F_B_C_2 := Parallelogram_D_F_B_C).
	destruct Parallelogram_D_F_B_C_2 as (Par_DF_BC & Par_DC_FB).

	pose proof (by_prop_Par_NC _ _ _ _ Par_DF_BC) as (nCol_D_F_B & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_D_F_B) as (_ & _ & nCol_B_D_F & _ & _).

	pose proof (proposition_34 _ _ _ _ Parallelogram_E_B_C_A) as (_ & _ & _ & _ & CongTriangles_BEA_ACB).
	pose proof (proposition_34 _ _ _ _ Parallelogram_F_B_C_D) as (_ & _ & _ & _ & CongTriangles_BFD_DCB).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_BEA_ACB) as EqAreaTri_BEA_ACB.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_BFD_DCB) as EqAreaTri_BFD_DCB.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_BEA_ACB) as (EqAreaTri_BEA_CBA & _ & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_BEA_CBA) as EqAreaTri_CBA_BEA.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_CBA_BEA) as (_ & EqAreaTri_CBA_BAE & _ & _ & _).
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_BFD_DCB) as (EqAreaTri_BFD_CBD & _ & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_BFD_CBD) as EqAreaTri_CBD_BFD.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_CBD_BFD) as (_ & EqAreaTri_CBD_BDF & _ & _ & _).

	pose proof (proposition_35 _ _ _ _ _ _ Parallelogram_E_B_C_A Parallelogram_F_B_C_D Col_E_A_F Col_E_A_D) as EqAreaQuad_EBCA_FBCD.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_EBCA_FBCD) as (_ & _ & _ & _ & _ & EqAreaQuad_EBCA_CBFD & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_EBCA_CBFD) as EqAreaQuad_CBFD_EBCA.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_CBFD_EBCA) as (_ & _ & _ & _ & _ & EqAreaQuad_CBFD_CBEA & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_CBFD_CBEA) as EqAreaQuad_CBEA_CBFD.

	pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_E_B_C_A) as (M & BetS_E_M_C & BetS_B_M_A).
	pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_F_B_C_D) as (m & BetS_F_m_C & BetS_B_m_D).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_M_A) as Col_B_M_A.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_m_D) as Col_B_m_D.
	pose proof (by_prop_Col_order _ _ _ Col_B_M_A) as (_ & _ & _ & Col_B_A_M & _).
	pose proof (by_prop_Col_order _ _ _ Col_B_m_D) as (_ & _ & _ & Col_B_D_m & _).

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_E_M_C Col_B_A_M nCol_B_A_E) as OppositeSide_E_BA_C.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_E_BA_C) as OppositeSide_C_BA_E.
	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_F_m_C Col_B_D_m nCol_B_D_F) as OppositeSide_F_BD_C.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_F_BD_C) as OppositeSide_C_BD_F.

	pose proof (axiom_halvesofequals _ _ _ _ _ _ _ _ EqAreaTri_CBA_BAE OppositeSide_C_BA_E EqAreaTri_CBD_BDF OppositeSide_C_BD_F EqAreaQuad_CBEA_CBFD) as EqAreaTri_CBA_CBD.

	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_CBA_CBD) as (_ & _ & _ & EqAreaTri_CBA_DBC & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_CBA_DBC) as EqAreaTri_DBC_CBA.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_DBC_CBA) as (_ & _ & _ & EqAreaTri_DBC_ABC & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_DBC_ABC) as EqAreaTri_ABC_DBC.

	exact EqAreaTri_ABC_DBC.
Qed.

End Euclid.
