Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Par.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_def_SameSide.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_collinear2.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_flip.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_rotate.
Require Import ProofCheckingEuclid.by_prop_SameSide_flip.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Playfair.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_diagonalsbisect.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_parallelbetween.
Require Import ProofCheckingEuclid.lemma_samesidecollinear.
Require Import ProofCheckingEuclid.lemma_samesidetransitive.
Require Import ProofCheckingEuclid.lemma_triangletoparallelogram.
Require Import ProofCheckingEuclid.proposition_15.
Require Import ProofCheckingEuclid.proposition_30.
Require Import ProofCheckingEuclid.proposition_31.
Require Import ProofCheckingEuclid.proposition_33B.
Require Import ProofCheckingEuclid.proposition_34.
Require Import ProofCheckingEuclid.proposition_43.
Require Import ProofCheckingEuclid.proposition_43B.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_44A :
	forall A B D E F G J N,
	Parallelogram B E F G ->
	CongA E B G J D N ->
	BetS A B E ->
	exists X Y, Parallelogram A B X Y /\ CongA A B X J D N /\ EqAreaQuad B E F G Y X B A /\ BetS G B X.
Proof.
	intros A B D E F G J N.
	intros Parallelogram_B_E_F_G.
	intros CongA_EBG_JDN.
	intros BetS_A_B_E.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq E E) as eq_E_E by (reflexivity).
	assert (eq F F) as eq_F_F by (reflexivity).
	assert (eq G G) as eq_G_G by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C G B G eq_G_G) as Col_G_B_G.
	pose proof (by_def_Col_from_eq_B_C A B B eq_B_B) as Col_A_B_B.
	pose proof (by_def_Col_from_eq_B_C B E E eq_E_E) as Col_B_E_E.
	pose proof (by_def_Col_from_eq_B_C E B B eq_B_B) as Col_E_B_B.
	pose proof (by_def_Col_from_eq_B_C F E E eq_E_E) as Col_F_E_E.
	pose proof (by_def_Col_from_eq_B_C G B B eq_B_B) as Col_G_B_B.
	pose proof (by_def_Col_from_eq_B_C G F F eq_F_F) as Col_G_F_F.

	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_B_E_F_G) as Parallelogram_E_F_G_B.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_E_F_G_B) as Parallelogram_F_G_B_E.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_F_G_B_E) as Parallelogram_G_B_E_F.

	pose proof (proposition_34 _ _ _ _ Parallelogram_G_B_E_F) as (_ & Cong_GB_FE & _ & _ & _).

	assert (Parallelogram_G_B_E_F_2 := Parallelogram_G_B_E_F).
	destruct Parallelogram_G_B_E_F_2 as (Par_GB_EF & Par_GF_BE).

	pose proof (by_prop_Par_flip _ _ _ _ Par_GB_EF) as (_ & Par_GB_FE & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_GB_FE) as Par_FE_GB.

	pose proof (by_prop_Par_flip _ _ _ _ Par_GF_BE) as (_ & Par_GF_EB & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_GF_BE) as Par_BE_GF.
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_BE_GF) as TarskiPar_BE_GF.
	pose proof (by_prop_Par_NC _ _ _ _ Par_GF_EB) as (_ & _ & nCol_F_E_B & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_F_E_B) as (neq_F_E & _ & _ & _ & _ & _).

	pose proof (by_prop_Par_NC _ _ _ _ Par_GF_BE) as (_ & nCol_G_B_E & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_G_B_E) as (_ & _ & _ & _ & nCol_E_B_G).
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_G_B_E) as CongA_GBE_EBG.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_G_B_E) as (neq_G_B & _ & _ & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_E_B_G) as (_ & neq_B_G & _ & _ & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_E) as BetS_E_B_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_B_E) as (neq_B_E & neq_A_B & neq_A_E).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_B_A) as (neq_B_A & neq_E_B & neq_E_A).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_B_E) as Col_A_B_E.
	pose proof (by_prop_Col_order _ _ _ Col_A_B_E) as (Col_B_A_E & Col_B_E_A & Col_E_A_B & Col_A_E_B & Col_E_B_A).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_E_B_G Col_E_B_A Col_E_B_B neq_A_B) as nCol_A_B_G.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_G) as (_ & _ & _ & _ & nCol_G_B_A).

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_GF_EB Col_E_B_A neq_A_B) as Par_GF_AB.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_GF_AB) as Par_AB_GF.

	pose proof (lemma_extension _ _ _ _ neq_G_B neq_G_B) as (q & BetS_G_B_q & Cong_Bq_GB).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_B_q) as BetS_q_B_G.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_G_B_q) as (neq_B_q & _ & neq_G_q).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_q_B_G) as (_ & neq_q_B & neq_q_G).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_G_B_q) as Col_G_B_q.
	pose proof (by_prop_Col_order _ _ _ Col_G_B_q) as (Col_B_G_q & Col_B_q_G & Col_q_G_B & Col_G_q_B & Col_q_B_G).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_G_B_A Col_G_B_q Col_G_B_G neq_q_G) as nCol_q_G_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_q_G_A) as (nCol_G_q_A & _ & _ & _ & _).

	pose proof (proposition_31 _ _ _ _ BetS_G_B_q nCol_G_q_A) as (
		H & h & T &
		BetS_H_A_h &
		CongA_hAB_ABG & CongA_hAB_GBA & CongA_BAh_GBA &
		CongA_HAB_ABq & CongA_HAB_qBA & CongA_BAH_qBA &
		Par_Hh_Gq &
		Cong_HA_Bq & Cong_Ah_GB & Cong_AT_TB & Cong_HT_Tq & Cong_GT_Th &
		BetS_H_T_q & BetS_G_T_h & BetS_A_T_B
	).

	assert (eq H H) as eq_H_H by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C A H H eq_H_H) as Col_A_H_H.
	pose proof (by_def_Col_from_eq_B_C H A A eq_A_A) as Col_H_A_A.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_A_h) as BetS_h_A_H.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_H_A_h) as (neq_A_h & neq_H_A & neq_H_h).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_h_A_H) as (neq_A_H & neq_h_A & neq_h_H).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_H_A_h) as Col_H_A_h.
	pose proof (by_prop_Col_order _ _ _ Col_H_A_h) as (Col_A_H_h & Col_A_h_H & Col_h_H_A & Col_H_h_A & Col_h_A_H).

	pose proof (by_prop_Par_flip _ _ _ _ Par_Hh_Gq) as (_ & Par_Hh_qG & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_Hh_qG Col_q_G_B neq_B_G) as Par_Hh_BG.
	pose proof (by_prop_Par_flip _ _ _ _ Par_Hh_BG) as (_ & Par_Hh_GB & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_Hh_GB) as Par_GB_Hh.
	pose proof (by_prop_Par_flip _ _ _ _ Par_GB_Hh) as (_ & Par_GB_hH & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_GB_hH Col_h_H_A neq_A_H) as Par_GB_AH.
	pose proof (by_prop_Par_flip _ _ _ _ Par_GB_AH) as (_ & Par_GB_HA & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_GB_HA) as Par_HA_GB.
	pose proof (by_prop_Par_flip _ _ _ _ Par_HA_GB) as (_ & Par_HA_BG & _).

	pose proof (by_prop_Par_NC _ _ _ _ Par_GB_HA) as (_ & _ & nCol_B_H_A & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_B_H_A) as (_ & _ & nCol_A_B_H & _ & _).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_T_B) as Col_A_T_B.
	pose proof (by_prop_Col_order _ _ _ Col_A_T_B) as (_ & _ & _ & Col_A_B_T & _).

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_HA_Bq Cong_Bq_GB) as Cong_HA_GB.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_HA_GB Cong_GB_FE) as Cong_HA_FE.

	pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_A_B_T Col_A_B_B BetS_H_T_q BetS_G_B_q nCol_A_B_H nCol_A_B_G) as SameSide_H_G_AB.
	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_H_G_AB Col_A_B_E neq_A_E) as SameSide_H_G_AE.

	assert (TarskiPar_BE_GF_2 := TarskiPar_BE_GF).
	destruct TarskiPar_BE_GF_2 as (_ & neq_G_F & n_Meet_B_E_G_F & SameSide_G_F_BE).

	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_G_F_BE) as SameSide_G_F_EB.
	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_G_F_EB Col_E_B_A neq_E_A) as SameSide_G_F_EA.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_G_F_EA) as SameSide_G_F_AE.
	pose proof (lemma_samesidetransitive _ _ _ _ _ SameSide_H_G_AE SameSide_G_F_AE) as SameSide_H_F_AE.

	pose proof (proposition_33B _ _ _ _ Par_HA_GB Cong_HA_GB SameSide_H_G_AB) as (Par_HG_AB & Cong_HG_AB).

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_HG_AB) as Par_AB_HG.
	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_HG) as (_ & Par_AB_GH & _).

	pose proof (lemma_Playfair _ _ _ _ _ Par_AB_GH Par_AB_GF) as Col_G_H_F.
	pose proof (by_prop_Col_order _ _ _ Col_G_H_F) as (_ & Col_H_F_G & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_G_H_F) as (Col_H_G_F & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_H_F_G) as (_ & Col_F_G_H & _ & _ & _).

	pose proof (by_def_Parallelogram _ _ _ _ Par_HA_BG Par_HG_AB) as Parallelogram_H_A_B_G.
	pose proof (by_prop_Parallelogram_flip _ _ _ _ Parallelogram_H_A_B_G) as Parallelogram_A_H_G_B.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_H_A_B_G) as Parallelogram_A_B_G_H.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_A_B_G_H) as Parallelogram_B_G_H_A.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_B_G_H_A) as Parallelogram_G_H_A_B.

	pose proof (proposition_30 _ _ _ _ _ _ _ _ _ Par_HA_GB Par_FE_GB BetS_A_B_E Col_H_A_A Col_G_B_B Col_F_E_E neq_H_A neq_G_B neq_F_E) as Par_HA_FE.

	pose proof (proposition_33B _ _ _ _ Par_HA_FE Cong_HA_FE SameSide_H_F_AE) as (Par_HF_AE & _).
	pose proof (by_prop_Par_flip _ _ _ _ Par_HA_FE) as (_ & Par_HA_EF & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_HA_FE) as (_ & nCol_H_F_E & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_H_F_E) as (_ & _ & _ & _ & nCol_E_F_H).
	pose proof (by_prop_nCol_order _ _ _ nCol_E_F_H) as (_ & _ & nCol_H_E_F & _ & _).

	pose proof (by_def_Parallelogram _ _ _ _ Par_HA_EF Par_HF_AE) as Parallelogram_H_A_E_F.
	pose proof (lemma_diagonalsbisect _ _ _ _ Parallelogram_H_A_E_F) as (t & Midpoint_H_t_E & Midpoint_A_t_F).

	destruct Midpoint_H_t_E as (BetS_H_t_E & Cong_Ht_tE).
	destruct Midpoint_A_t_F as (BetS_A_t_F & Cong_At_tF).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_Ht_tE) as (_ & _ & Cong_Ht_Et).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_At_tF) as (_ & _ & Cong_At_Ft).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_At_Ft) as (Cong_tA_tF & _ & _).

	pose proof (postulate_Euclid5 _ _ _ _ _ _ BetS_A_t_F BetS_H_t_E BetS_A_B_E Cong_Ht_Et Cong_tA_tF nCol_H_E_F) as (K & BetS_H_B_K & BetS_F_E_K).

	assert (eq K K) as eq_K_K by (reflexivity).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_B_K) as BetS_K_B_H.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_E_K) as BetS_K_E_F.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_F_E_K) as (neq_E_K & _ & neq_F_K).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_K_E_F) as (neq_E_F & neq_K_E & neq_K_F).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_F_E_K) as Col_F_E_K.
	pose proof (by_prop_Col_order _ _ _ Col_F_E_K) as (Col_E_F_K & Col_E_K_F & Col_K_F_E & Col_F_K_E & Col_K_E_F).

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_HA_EF Col_E_F_K neq_K_F) as Par_HA_KF.
	pose proof (by_prop_Par_flip _ _ _ _ Par_HA_KF) as (_ & Par_HA_FK & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_HA_FK) as Par_FK_HA.
	pose proof (by_prop_Par_flip _ _ _ _ Par_FK_HA) as (_ & Par_FK_AH & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_GB_EF Col_E_F_K neq_K_F) as Par_GB_KF.

	pose proof (lemma_triangletoparallelogram _ _ _ _ _ Par_FK_AH Col_A_H_H) as (L & Parallelogram_H_L_K_F & Col_A_H_L).

	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_H_L_K_F) as Parallelogram_L_K_F_H.
	pose proof (by_prop_Parallelogram_flip _ _ _ _ Parallelogram_L_K_F_H) as Parallelogram_K_L_H_F.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_K_L_H_F) as Parallelogram_L_H_F_K.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_L_H_F_K) as Parallelogram_H_F_K_L.

	pose proof (by_prop_Col_order _ _ _ Col_A_H_L) as (_ & _ & Col_L_A_H & _ & _).

	assert (Parallelogram_H_L_K_F_2 := Parallelogram_H_L_K_F).
	destruct Parallelogram_H_L_K_F_2 as (Par_HL_KF & Par_HF_LK).

	pose proof (by_prop_Par_NC _ _ _ _ Par_HL_KF) as (_ & _ & nCol_L_K_F & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_HL_KF) as (nCol_H_L_K & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_H_L_K) as (_ & _ & _ & neq_L_H & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_L_K_F) as (neq_L_K & _ & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_L_K) as neq_K_L.

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_HF_LK) as Par_LK_HF.
	pose proof (by_prop_Par_flip _ _ _ _ Par_LK_HF) as (Par_KL_HF & _ & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_KL_HF Col_H_F_G neq_G_F) as Par_KL_GF.
	pose proof (by_prop_Par_flip _ _ _ _ Par_KL_GF) as (_ & Par_KL_FG & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_KL_FG) as Par_FG_KL.

	assert (Par_HF_LK_2 := Par_HF_LK).
	destruct Par_HF_LK_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_H_F_L_K & _ & _).

	pose proof (by_prop_Par_collinear2 _ _ _ _ _ _ Par_GB_FE Col_F_E_E Col_F_E_K neq_E_K) as Par_GB_EK.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_GB_EK) as Par_EK_GB.
	pose proof (lemma_triangletoparallelogram _ _ _ _ _ Par_EK_GB Col_G_B_B) as (M & Parallelogram_B_M_K_E & Col_G_B_M).

	pose proof (by_def_Col_from_eq_B_C M K K eq_K_K) as Col_M_K_K.

	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_B_M_K_E) as Parallelogram_M_K_E_B.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_M_K_E_B) as Parallelogram_K_E_B_M.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_K_E_B_M) as Parallelogram_E_B_M_K.
	pose proof (by_prop_Parallelogram_flip _ _ _ _ Parallelogram_B_M_K_E) as Parallelogram_M_B_E_K.

	pose proof (by_prop_Col_order _ _ _ Col_G_B_M) as (_ & _ & _ & Col_G_M_B & _).


	assert (Parallelogram_B_M_K_E_2 := Parallelogram_B_M_K_E).
	destruct Parallelogram_B_M_K_E_2 as (Par_BM_KE & Par_BE_MK).

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_BE_MK) as Par_MK_BE.
	pose proof (by_prop_Par_NC _ _ _ _ Par_BE_MK) as (_ & _ & nCol_E_M_K & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_BE_MK) as (_ & nCol_B_M_K & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_M_K) as (_ & _ & _ & neq_M_B & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_E_M_K) as (_ & neq_M_K & _ & _ & _ & _).

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_HA_GB Col_G_B_M neq_M_B) as Par_HA_MB.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_HA_MB) as Par_MB_HA.
	pose proof (by_prop_Par_flip _ _ _ _ Par_MB_HA) as (_ & Par_MB_AH & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_MB_AH Col_A_H_L neq_L_H) as Par_MB_LH.
	pose proof (by_prop_Par_flip _ _ _ _ Par_MB_LH) as (_ & Par_MB_HL & _).

	pose proof (proposition_30 _ _ _ _ _ _ _ _ _ Par_MK_BE Par_GF_BE BetS_K_E_F Col_M_K_K Col_B_E_E Col_G_F_F neq_M_K neq_B_E neq_G_F) as Par_MK_GF.
	pose proof (by_prop_Par_flip _ _ _ _ Par_MK_GF) as (_ & _ & Par_KM_FG).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_KM_FG) as Par_FG_KM.

	pose proof (lemma_Playfair _ _ _ _ _ Par_FG_KM Par_FG_KL) as Col_K_M_L.
	pose proof (by_prop_Col_order _ _ _ Col_K_M_L) as (Col_M_K_L & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_M_K_L) as (_ & _ & Col_L_M_K & _ & _).

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_BE_MK Col_M_K_L neq_L_K) as Par_BE_LK.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_BE_LK) as Par_LK_BE.
	pose proof (by_prop_Par_flip _ _ _ _ Par_LK_BE) as (_ & Par_LK_EB & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_LK_EB Col_E_B_A neq_A_B) as Par_LK_AB.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_LK_AB) as Par_AB_LK.
	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_LK) as (_ & Par_AB_KL & _).

	pose proof (lemma_parallelbetween _ _ _ _ _ BetS_H_B_K Par_MB_HL Col_L_M_K) as BetS_L_M_K.
	pose proof (lemma_parallelbetween _ _ _ _ _ BetS_K_B_H Par_AB_KL Col_L_A_H) as BetS_L_A_H.
	pose proof (lemma_parallelbetween _ _ _ _ _ BetS_K_B_H Par_GB_KF Col_F_G_H) as BetS_F_G_H.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_L_A_H) as BetS_H_A_L.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_G_H) as BetS_H_G_F.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_H_G_F) as (_ & _ & neq_H_F).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_H_G_F) as (_ & neq_H_G & _).

	pose proof (
		proposition_43
		_ _ _ _ _ _ _ _ _
		Parallelogram_H_F_K_L
		BetS_H_A_L BetS_H_G_F BetS_L_M_K BetS_F_E_K BetS_H_B_K
		Parallelogram_G_H_A_B Parallelogram_E_B_M_K
	) as EqAreaQuad_B_E_F_G_L_M_B_A.
	pose proof (
		proposition_43B
		_ _ _ _ _ _ _ _ _
		Parallelogram_H_L_K_F
		BetS_H_G_F BetS_H_A_L BetS_F_E_K BetS_L_M_K
		Parallelogram_A_H_G_B Parallelogram_M_B_E_K
	) as Parallelogram_A_B_M_L.

	pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_H_G_F Col_L_M_K neq_H_F neq_L_K neq_H_G neq_M_K n_Meet_H_F_L_K BetS_H_B_K Col_G_M_B) as BetS_G_B_M.
	pose proof (proposition_15 _ _ _ _ _ BetS_G_B_M BetS_A_B_E nCol_G_B_A) as (_ & CongA_ABM_GBE).
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABM_GBE CongA_GBE_EBG) as CongA_ABM_EBG.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABM_EBG CongA_EBG_JDN) as CongA_ABM_JDN.

	exists M, L.
	split.
	exact Parallelogram_A_B_M_L.
	split.
	exact CongA_ABM_JDN.
	split.
	exact EqAreaQuad_B_E_F_G_L_M_B_A.
	exact BetS_G_B_M.
Qed.

End Euclid.
