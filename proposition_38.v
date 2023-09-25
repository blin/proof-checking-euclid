Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear2.
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
Require Import ProofCheckingEuclid.proposition_36.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_38 :
	forall A B C D E F P Q,
	Par P Q B C ->
	Col P Q A ->
	Col P Q D ->
	Cong B C E F ->
	Col B C E ->
	Col B C F ->
	EqAreaTri A B C D E F.
Proof.
	intros A B C D E F P Q.
	intros Par_PQ_BC.
	intros Col_P_Q_A.
	intros Col_P_Q_D.
	intros Cong_BC_EF.
	intros Col_B_C_E.
	intros Col_B_C_F.

	pose proof (by_prop_Par_flip _ _ _ _ Par_PQ_BC) as (Par_QP_BC & Par_PQ_CB & Par_QP_CB).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_PQ_BC) as Par_BC_PQ.
	pose proof (by_prop_Par_flip _ _ _ _ Par_BC_PQ) as (Par_CB_PQ & Par_BC_QP & Par_CB_QP).
	pose proof (by_prop_Par_NC _ _ _ _ Par_PQ_BC) as (nCol_P_Q_B & nCol_P_B_C & nCol_Q_B_C & nCol_P_Q_C).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_P_B_C) as (neq_P_B & neq_B_C & neq_P_C & neq_B_P & neq_C_B & neq_C_P).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_P_Q_B) as (neq_P_Q & _ & _ & _ & _ & _).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BC_EF) as (_ & _ & Cong_BC_FE).

	pose proof (lemma_triangletoparallelogram _ _ _ _ _ Par_CB_PQ Col_P_Q_A) as (G & Parallelogram_A_G_B_C & Col_P_Q_G).

	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_A_G_B_C) as Parallelogram_G_B_C_A.

	assert (Parallelogram_A_G_B_C_2 := Parallelogram_A_G_B_C).
	destruct Parallelogram_A_G_B_C_2 as (Par_AG_BC & Par_AC_GB).

	pose proof (by_prop_Par_NC _ _ _ _ Par_AG_BC) as (nCol_A_G_B & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_G_B) as (_ & _ & nCol_B_A_G & _ & _).

	pose proof (axiom_nocollapse _ _ _ _ neq_B_C Cong_BC_EF) as neq_E_F.

	pose proof (by_prop_Par_collinear2 _ _ _ _ _ _ Par_PQ_BC Col_B_C_E Col_B_C_F neq_E_F) as Par_PQ_EF.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_PQ_EF) as Par_EF_PQ.

	pose proof (lemma_triangletoparallelogram _ _ _ _ _ Par_EF_PQ Col_P_Q_D) as (H & Parallelogram_D_H_F_E & Col_P_Q_H).

	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_D_H_F_E) as Parallelogram_H_F_E_D.

	assert (Parallelogram_D_H_F_E_2 := Parallelogram_D_H_F_E).
	destruct Parallelogram_D_H_F_E_2 as (Par_DH_FE & Par_DE_HF).

	pose proof (by_prop_Par_NC _ _ _ _ Par_DH_FE) as (nCol_D_H_F & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_D_H_F) as (_ & _ & nCol_F_D_H & _ & _).

	pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_P_Q Col_P_Q_G Col_P_Q_A Col_P_Q_H) as Col_G_A_H.
	pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_P_Q Col_P_Q_G Col_P_Q_A Col_P_Q_D) as Col_G_A_D.

	pose proof (proposition_36 _ _ _ _ _ _ _ _ Parallelogram_G_B_C_A Parallelogram_H_F_E_D Col_G_A_H Col_G_A_D Col_B_C_F Col_B_C_E Cong_BC_FE) as EqAreaQuad_G_B_C_A_H_F_E_D.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_G_B_C_A_H_F_E_D) as (_ & _ & _ & _ & _ & EqAreaQuad_G_B_C_A_E_F_H_D & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_G_B_C_A_E_F_H_D) as EqAreaQuad_E_F_H_D_G_B_C_A.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_E_F_H_D_G_B_C_A) as (_ & _ & _ & _ & _ & EqAreaQuad_E_F_H_D_C_B_G_A & _).

	pose proof (proposition_34 _ _ _ _ Parallelogram_H_F_E_D) as (_ & _ & _ & _ & CongTriangles_FHD_DEF).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_FHD_DEF) as EqAreaTri_F_H_D_D_E_F.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_F_H_D_D_E_F) as (EqAreaTri_F_H_D_E_F_D & _ & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_F_H_D_E_F_D) as EqAreaTri_E_F_D_F_H_D.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_E_F_D_F_H_D) as (_ & EqAreaTri_E_F_D_F_D_H & _ & _ & _).

	pose proof (proposition_34 _ _ _ _ Parallelogram_G_B_C_A) as (_ & _ & _ & _ & CongTriangles_BGA_ACB).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_BGA_ACB) as EqAreaTri_B_G_A_A_C_B.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_B_G_A_A_C_B) as (EqAreaTri_B_G_A_C_B_A & _ & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_B_G_A_C_B_A) as EqAreaTri_C_B_A_B_G_A.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_C_B_A_B_G_A) as (_ & EqAreaTri_C_B_A_B_A_G & _ & _ & _).

	pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_D_H_F_E) as (M & BetS_D_M_F & BetS_H_M_E).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_D_M_F) as Col_D_M_F.
	pose proof (by_prop_Col_order _ _ _ Col_D_M_F) as (_ & _ & Col_F_D_M & _ & _).

	pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_A_G_B_C) as (m & BetS_A_m_B & BetS_G_m_C).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_m_B) as Col_A_m_B.
	pose proof (by_prop_Col_order _ _ _ Col_A_m_B) as (_ & _ & Col_B_A_m & _ & _).

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_G_m_C Col_B_A_m nCol_B_A_G) as OppositeSide_G_BA_C.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_G_BA_C) as OppositeSide_C_BA_G.
	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_H_M_E Col_F_D_M nCol_F_D_H) as OppositeSide_H_FD_E.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_H_FD_E) as OppositeSide_E_FD_H.

	pose proof (axiom_halvesofequals _ _ _ _ _ _ _ _ EqAreaTri_E_F_D_F_D_H OppositeSide_E_FD_H EqAreaTri_C_B_A_B_A_G OppositeSide_C_BA_G EqAreaQuad_E_F_H_D_C_B_G_A) as EqAreaTri_E_F_D_C_B_A.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_E_F_D_C_B_A) as (_ & _ & _ & EqAreaTri_E_F_D_A_B_C & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_E_F_D_A_B_C) as EqAreaTri_A_B_C_E_F_D.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_A_B_C_E_F_D) as (_ & _ & _ & _ & EqAreaTri_A_B_C_D_E_F).

	exact EqAreaTri_A_B_C_D_E_F.
Qed.

End Euclid.
