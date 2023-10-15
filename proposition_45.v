Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Midpoint.
Require Import ProofCheckingEuclid.by_def_OnRay.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol .
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_SumTwoRT_congruence.
Require Import ProofCheckingEuclid.by_prop_SumTwoRT_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Playfair.
Require Import ProofCheckingEuclid.lemma_diagonalsmeet.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB .
Require Import ProofCheckingEuclid.lemma_samesidecollinear.
Require Import ProofCheckingEuclid.proposition_10.
Require Import ProofCheckingEuclid.proposition_14.
Require Import ProofCheckingEuclid.proposition_29C.
Require Import ProofCheckingEuclid.proposition_30.
Require Import ProofCheckingEuclid.proposition_42B.
Require Import ProofCheckingEuclid.proposition_44.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_45 :
	forall A B C D E J K N O R S,
	nCol J E N ->
	nCol A B D ->
	nCol C B D ->
	BetS A O C ->
	BetS B O D ->
	neq R K ->
	nCol K R S ->
	exists X Z U, Parallelogram X K Z U /\ CongA X K Z J E N /\ EqAreaQuad X K Z U A B C D /\ OnRay K R Z /\ SameSide X S K Z.
Proof.
	intros A B C D E J K N O R S.
	intros nCol_J_E_N.
	intros nCol_A_B_D.
	intros nCol_C_B_D.
	intros BetS_A_O_C.
	intros BetS_B_O_D.
	intros neq_R_K.
	intros nCol_K_R_S.

	assert (eq K K) as eq_K_K by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C R K K eq_K_K) as Col_R_K_K.

	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_D) as (nCol_B_A_D & nCol_B_D_A & nCol_D_A_B & nCol_A_D_B & nCol_D_B_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_D) as (neq_A_B & neq_B_D & neq_A_D & neq_B_A & neq_D_B & neq_D_A).

	pose proof (by_def_Triangle _ _ _ nCol_A_B_D) as Triangle_ABD.

	pose proof (by_prop_nCol_order _ _ _ nCol_C_B_D) as (nCol_B_C_D & nCol_B_D_C & nCol_D_C_B & nCol_C_D_B & nCol_D_B_C).

	pose proof (by_def_Triangle _ _ _ nCol_D_B_C) as Triangle_DBC.

	pose proof (by_prop_nCol_order _ _ _ nCol_K_R_S) as (nCol_R_K_S & _ & _ & _ & _).

	pose proof (proposition_10 _ _ neq_B_D) as (m & BetS_B_m_D & Cong_mB_mD).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_m_D) as (_ & neq_B_m & _).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_mB_mD) as (_ & Cong_Bm_mD & _).
	pose proof (by_def_Midpoint _ _ _ BetS_B_m_D Cong_Bm_mD) as Midpoint_B_m_D.

	pose proof (lemma_extension _ _ _ _ neq_R_K neq_B_m) as (P & BetS_R_K_P & Cong_KP_Bm).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_R_K_P) as BetS_P_K_R.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_R_K_P) as (neq_K_P & _ & neq_R_P).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_P_K_R) as (neq_K_R & neq_P_K & neq_P_R).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_R_K_P) as Col_R_K_P.
	pose proof (by_prop_Col_order _ _ _ Col_R_K_P) as (Col_K_R_P & Col_K_P_R & Col_P_R_K & Col_R_P_K & Col_P_K_R).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_KP_Bm) as (_ & Cong_PK_Bm & _).

	pose proof (lemma_extension _ _ _ _ neq_P_K neq_P_K) as (H & BetS_P_K_H & Cong_KH_PK).

	assert (eq H H) as eq_H_H by (reflexivity).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_K_H) as BetS_H_K_P.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_P_K_H) as (neq_K_H & _ & neq_P_H).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_H_K_P) as (_ & neq_H_K & neq_H_P).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_P_K_H) as Col_P_K_H.
	pose proof (by_prop_Col_order _ _ _ Col_P_K_H) as (Col_K_P_H & Col_K_H_P & Col_H_P_K & Col_P_H_K & Col_H_K_P).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_KH_PK) as Cong_PK_KH.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_KH_PK Cong_PK_Bm) as Cong_KH_Bm.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_KH_Bm Cong_Bm_mD) as Cong_KH_mD.

	pose proof (by_def_Midpoint _ _ _ BetS_P_K_H Cong_PK_KH) as Midpoint_P_K_H.

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_P_K_H Col_P_K_R neq_P_K) as Col_K_H_R.
	pose proof (by_prop_Col_order _ _ _ Col_K_H_R) as (_ & _ & Col_R_K_H & _ & _).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_R_K_S Col_R_K_H Col_R_K_K neq_H_K) as nCol_H_K_S.
	pose proof (by_prop_nCol_order _ _ _ nCol_H_K_S) as (_ & _ & _ & _ & nCol_S_K_H).

	pose proof (proposition_42B _ _ _ _ _ _ _ _ _ _ _ Triangle_ABD Midpoint_B_m_D nCol_J_E_N Midpoint_P_K_H Cong_KH_mD nCol_S_K_H) as (
		F & G & Parallelogram_F_K_H_G & EqAreaQuad_A_B_m_D_F_K_H_G & CongA_HKF_JEN & SameSide_S_F_KH
	).

	pose proof (by_def_Col_from_eq_B_C F K K eq_K_K) as Col_F_K_K.
	pose proof (by_def_Col_from_eq_B_C G H H eq_H_H) as Col_G_H_H.

	assert (Parallelogram_F_K_H_G_2 := Parallelogram_F_K_H_G).
	destruct Parallelogram_F_K_H_G_2 as (Par_FK_HG & Par_FG_KH).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_S_F_KH) as (SameSide_F_S_KH & _ & _).

	pose proof (by_prop_Par_flip _ _ _ _ Par_FK_HG) as (Par_KF_HG & Par_FK_GH & Par_KF_GH).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_FK_HG) as Par_HG_FK.
	pose proof (by_prop_Par_flip _ _ _ _ Par_HG_FK) as (Par_GH_FK & Par_HG_KF & Par_GH_KF).
	pose proof (by_prop_Par_NC _ _ _ _ Par_FK_HG) as (nCol_F_K_H & nCol_F_H_G & nCol_K_H_G & nCol_F_K_G).

	pose proof (by_prop_nCol_order _ _ _ nCol_K_H_G) as (nCol_H_K_G & nCol_H_G_K & nCol_G_K_H & nCol_K_G_H & nCol_G_H_K).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_F_K_H) as (neq_F_K & _ & _ & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_H_G_K) as (neq_H_G & _ & _ & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_G_H_K) as (neq_G_H & _ & _ & _ & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_H_G) as OnRay_HG_G.

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_F_K_H) as CongA_FKH_HKF.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_FKH_HKF CongA_HKF_JEN) as CongA_FKH_JEN.

	pose proof (by_prop_Par_flip _ _ _ _ Par_FG_KH) as (_ & Par_FG_HK & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_FG_KH) as Par_KH_FG.
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_KH_FG) as TarskiPar_KH_FG.

	assert (TarskiPar_KH_FG_2 := TarskiPar_KH_FG).
	destruct TarskiPar_KH_FG_2 as (_ & neq_F_G & n_Meet_K_H_F_G & SameSide_F_G_KH).

	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_GH_FK) as TarskiPar_GH_FK.

	assert (TarskiPar_GH_FK_2 := TarskiPar_GH_FK).
	destruct TarskiPar_GH_FK_2 as (_ & _ & n_Meet_G_H_F_K & SameSide_F_K_GH).

	pose proof (proposition_44 _ _ _ _ _ _ _ _ _ Triangle_DBC nCol_J_E_N nCol_G_H_K) as (
		M & L & e & Parallelogram_G_H_M_L & CongA_GHM_JEN & EqAreaQuad_D_B_e_C_G_H_M_L & Midpoint_B_e_C & OppositeSide_M_GH_K
	).

	assert (eq M M) as eq_M_M by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C L M M eq_M_M) as Col_L_M_M.

	assert (Parallelogram_G_H_M_L_2 := Parallelogram_G_H_M_L).
	destruct Parallelogram_G_H_M_L_2 as (Par_GH_ML & Par_GL_HM).

	pose proof (by_prop_Par_flip _ _ _ _ Par_GH_ML) as (Par_HG_ML & Par_GH_LM & Par_HG_LM).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_GH_ML) as Par_ML_GH.
	pose proof (by_prop_Par_flip _ _ _ _ Par_ML_GH) as (Par_LM_GH & Par_ML_HG & Par_LM_HG).
	pose proof (by_prop_Par_NC _ _ _ _ Par_GH_ML) as (nCol_G_H_M & nCol_G_M_L & nCol_H_M_L & nCol_G_H_L).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_H_M_L) as (_ & _ & _ & _ & neq_L_M & _).
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_G_H_L) as n_Col_G_H_L.

	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_GH_LM) as TarskiPar_GH_LM.

	assert (TarskiPar_GH_LM_2 := TarskiPar_GH_LM).
	destruct TarskiPar_GH_LM_2 as (_ & _ & n_Meet_G_H_L_M & SameSide_L_M_GH).

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_GHM_JEN) as CongA_JEN_GHM.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_HKF_JEN CongA_JEN_GHM) as CongA_HKF_GHM.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_HKF_GHM) as CongA_GHM_HKF.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_FKH_HKF CongA_HKF_GHM) as CongA_FKH_GHM.

	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_GHM_HKF) as nCol_H_K_F.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_H_K_F) as (_ & neq_K_F & _ & _ & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_K_F) as OnRay_KF_F.

	assert (Midpoint_B_e_C_2 := Midpoint_B_e_C).
	destruct Midpoint_B_e_C_2 as (BetS_B_e_C & Cong_Be_eC).

	pose proof (proposition_29C _ _ _ _ _ Par_KF_HG SameSide_F_G_KH BetS_P_K_H) as (_ & SumTwoRT_FKH_KHG).
	pose proof (by_prop_SumTwoRT_congruence _ _ _ _ _ _ _ _ _ SumTwoRT_FKH_KHG CongA_FKH_GHM) as SumTwoRT_GHM_KHG.
	pose proof (by_prop_SumTwoRT_symmetric _ _ _ _ _ _ SumTwoRT_GHM_KHG) as SumTwoRT_KHG_GHM.

	pose proof (proposition_14 _ _ _ _ _ SumTwoRT_KHG_GHM OnRay_HG_G OppositeSide_M_GH_K) as (_ & BetS_K_H_M).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_K_H_M) as BetS_M_H_K.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_K_H_M) as (neq_H_M & _ & neq_K_M).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_M_H_K) as (_ & neq_M_H & neq_M_K).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_K_H_M) as Col_K_H_M.
	pose proof (by_prop_Col_order _ _ _ Col_K_H_M) as (Col_H_K_M & Col_H_M_K & Col_M_K_H & Col_K_M_H & Col_M_H_K).

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_K_H_M neq_K_H) as OnRay_KH_M.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_KH_M) as OnRay_KM_H.

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_K_H_M Col_G_H_H nCol_G_H_K) as OppositeSide_K_GH_M.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_F_K_GH OppositeSide_K_GH_M) as OppositeSide_F_GH_M.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_F_GH_M) as OppositeSide_M_GH_F.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_L_M_GH OppositeSide_M_GH_F) as OppositeSide_L_GH_F.

	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_F_S_KH Col_K_H_M neq_K_M) as SameSide_F_S_KM.

	pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_P_K_H BetS_K_H_M) as BetS_P_K_M.
	pose proof (by_def_OnRay _ _ _ _ BetS_P_K_R BetS_P_K_M) as OnRay_KR_M.

	pose proof (
		proposition_30 _ _ _ _ _ _ _ _ _ Par_FK_GH Par_LM_GH BetS_K_H_M Col_F_K_K Col_G_H_H Col_L_M_M neq_F_K neq_G_H neq_L_M
	) as Par_FK_LM.

	pose proof (by_prop_Par_flip _ _ _ _ Par_FK_LM) as (Par_KF_LM & Par_FK_ML & Par_KF_ML).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_FK_LM) as Par_LM_FK.
	pose proof (by_prop_Par_flip _ _ _ _ Par_LM_FK) as (Par_ML_FK & Par_LM_KF & Par_ML_KF).
	pose proof (by_prop_Par_NC _ _ _ _ Par_FK_LM) as (nCol_F_K_L & nCol_F_L_M & nCol_K_L_M & nCol_F_K_M).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_F_L_M) as (_ & _ & _ & neq_L_F & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_F_L_M) as (neq_F_L & _ & _ & _ & _ & _).

	pose proof (by_prop_CongA_reflexive _ _ _ nCol_F_K_M) as CongA_FKM_FKM.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_FKM_FKM OnRay_KF_F OnRay_KM_H) as CongA_FKM_FKH.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_FKM_FKH CongA_FKH_JEN) as CongA_FKM_JEN.

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_FG_HK Col_H_K_M neq_M_K) as Par_FG_MK.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_FG_MK) as Par_MK_FG.
	pose proof (by_prop_Par_flip _ _ _ _ Par_MK_FG) as (_ & Par_MK_GF & _).

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_GL_HM Col_H_M_K neq_K_M) as Par_GL_KM.
	pose proof (by_prop_Par_flip _ _ _ _ Par_GL_KM) as (_ & Par_GL_MK & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_GL_MK) as Par_MK_GL.

	pose proof (lemma_Playfair _ _ _ _ _ Par_MK_GL Par_MK_GF) as Col_G_L_F.
	pose proof (by_prop_Col_order _ _ _ Col_G_L_F) as (Col_L_G_F & Col_L_F_G & Col_F_G_L & Col_G_F_L & Col_F_L_G).

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_MK_GF Col_G_F_L neq_L_F) as Par_MK_LF.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_MK_LF) as Par_LF_MK.
	pose proof (by_prop_Par_flip _ _ _ _ Par_LF_MK) as (_ & _ & Par_FL_KM).

	pose proof (by_def_Parallelogram _ _ _ _ Par_FK_ML Par_FL_KM) as Parallelogram_F_K_M_L.

	pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_F_K_M_L) as (j & BetS_F_j_M & BetS_K_j_L).

	destruct OppositeSide_L_GH_F as (t & BetS_L_t_F & Col_G_H_t & _).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_L_t_F) as Col_L_t_F.
	pose proof (by_prop_Col_order _ _ _ Col_L_t_F) as (_ & _ & Col_F_L_t & _ & _).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_F_L_G Col_F_L_t neq_F_L) as Col_L_G_t.
	pose proof (by_prop_Col_order _ _ _ Col_L_G_t) as (Col_G_L_t & Col_G_t_L & Col_t_L_G & Col_L_t_G & Col_t_G_L).

	pose proof (by_prop_Col_order _ _ _ Col_G_H_t) as (Col_H_G_t & Col_H_t_G & Col_t_G_H & Col_G_t_H & Col_t_H_G).

	pose proof (lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB _ _ _ _ Col_G_t_H Col_G_t_L nCol_G_H_L) as eq_G_t.

	assert (BetS L G F) as BetS_L_G_F by (rewrite eq_G_t; exact BetS_L_t_F).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_L_G_F) as BetS_F_G_L.

	pose proof (
		axiom_paste4
		A B C D
		F _ _ j
		K L M _ _ _
		EqAreaQuad_A_B_m_D_F_K_H_G
		EqAreaQuad_D_B_e_C_G_H_M_L
		BetS_A_O_C
		BetS_B_O_D
		BetS_K_H_M
		BetS_F_G_L
		BetS_B_m_D
		BetS_B_e_C
		BetS_F_j_M BetS_K_j_L
	) as EqAreaQuad_A_B_C_D_F_K_M_L.

	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_A_B_C_D_F_K_M_L) as EqAreaQuad_F_K_M_L_A_B_C_D.

	exists F, M, L.
	split.
	exact Parallelogram_F_K_M_L .
	split.
	exact CongA_FKM_JEN .
	split.
	exact EqAreaQuad_F_K_M_L_A_B_C_D .
	split.
	exact OnRay_KR_M .
	exact SameSide_F_S_KM.
Qed.

End Euclid.
