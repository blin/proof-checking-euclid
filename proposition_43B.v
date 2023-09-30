Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_flip.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_SameSide_flip.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_sameside_onray_EFAC_BFG_EGAC.
Require Import ProofCheckingEuclid.lemma_samesidecollinear.
Require Import ProofCheckingEuclid.lemma_samesidetransitive.
Require Import ProofCheckingEuclid.lemma_supplements_SumTwoRT.
Require Import ProofCheckingEuclid.proposition_28D.
Require Import ProofCheckingEuclid.proposition_29C.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_43B :
	forall A B C D E F G H K,
	Parallelogram A B C D ->
	BetS A H D ->
	BetS A E B ->
	BetS D F C ->
	BetS B G C ->
	Parallelogram E A H K ->
	Parallelogram G K F C ->
	Parallelogram E K G B.
Proof.
	intros A B C D E F G H K.
	intros Parallelogram_A_B_C_D.
	intros BetS_A_H_D.
	intros BetS_A_E_B.
	intros BetS_D_F_C.
	intros BetS_B_G_C.
	intros Parallelogram_E_A_H_K.
	intros Parallelogram_G_K_F_C.

	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).
	pose proof (by_def_Col_from_eq_A_B B B E eq_B_B) as Col_B_B_E.
	pose proof (by_def_Col_from_eq_B_C B C C eq_C_C) as Col_B_C_C.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_H_D) as (_ & neq_A_H & _).

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_A_H_D neq_A_H) as OnRay_AH_D.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_AH_D) as OnRay_AD_H.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_B) as BetS_B_E_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_E_B) as (neq_E_B & neq_A_E & neq_A_B).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_E_A) as (neq_E_A & neq_B_E & neq_B_A).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_E_B) as Col_A_E_B.
	pose proof (by_prop_Col_order _ _ _ Col_A_E_B) as (Col_E_A_B & Col_E_B_A & Col_B_A_E & Col_A_B_E & Col_B_E_A).

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_A_E_B neq_A_E) as OnRay_AE_B.
	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_E_A neq_B_E) as OnRay_BE_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_A) as OnRay_BA_A.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_BE_A) as OnRay_BA_E.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_F_C) as BetS_C_F_D.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_F_D) as (_ & neq_C_F & _).

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_C_F_D neq_C_F) as OnRay_CF_D.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_CF_D) as OnRay_CD_F.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_G_C) as BetS_C_G_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_G_C) as (neq_G_C & neq_B_G & neq_B_C).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_G_B) as (neq_G_B & neq_C_G & neq_C_B).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_G_C) as Col_B_G_C.
	pose proof (by_prop_Col_order _ _ _ Col_B_G_C) as (Col_G_B_C & Col_G_C_B & Col_C_B_G & Col_B_C_G & Col_C_G_B).

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_G_C neq_B_G) as OnRay_BG_C.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_BG_C) as OnRay_BC_G.

	assert (Parallelogram_A_B_C_D_2 := Parallelogram_A_B_C_D).
	destruct Parallelogram_A_B_C_D_2 as (Par_AB_CD & Par_AD_BC).

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AB_CD) as Par_CD_AB.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AD_BC) as Par_BC_AD.
	pose proof (by_prop_Par_flip _ _ _ _ Par_CD_AB) as (_ & Par_CD_BA & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AD_BC) as (_ & _ & nCol_D_B_C & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_D_B_C) as (_ & _ & _ & nCol_D_C_B & _).
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_D_C_B) as CongA_DCB_DCB.
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_AB_CD) as TarskiPar_AB_CD.
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_BC_AD) as TarskiPar_BC_AD.

	assert (TarskiPar_AB_CD_2 := TarskiPar_AB_CD).
	destruct TarskiPar_AB_CD_2 as (_ & neq_C_D & n_Meet_A_B_C_D & SameSide_C_D_AB).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_C_D_AB) as (SameSide_D_C_AB & _ & _).
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_C_D_AB) as SameSide_C_D_BA.

	assert (TarskiPar_BC_AD_2 := TarskiPar_BC_AD).
	destruct TarskiPar_BC_AD_2 as (_ & neq_A_D & n_Meet_B_C_A_D & SameSide_A_D_BC).

	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_A_D_BC) as SameSide_A_D_CB.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_A_D_CB) as (SameSide_D_A_CB & _ & _).

	assert (Parallelogram_E_A_H_K_2 := Parallelogram_E_A_H_K).
	destruct Parallelogram_E_A_H_K_2 as (Par_EA_HK & Par_EK_AH).

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_EK_AH) as Par_AH_EK.
	pose proof (by_prop_Par_NC _ _ _ _ Par_AH_EK) as (nCol_A_H_E & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_H_E) as (_ & _ & nCol_E_A_H & _ & _).
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_E_A_H) as CongA_EAH_EAH.
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_EA_HK) as TarskiPar_EA_HK.

	assert (TarskiPar_EA_HK_2 := TarskiPar_EA_HK).
	destruct TarskiPar_EA_HK_2 as (_ & neq_H_K & n_Meet_E_A_H_K & SameSide_H_K_EA).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_H_K_EA) as (_ & SameSide_H_K_AE & _).

	assert (Parallelogram_G_K_F_C_2 := Parallelogram_G_K_F_C).
	destruct Parallelogram_G_K_F_C_2 as (Par_GK_FC & Par_GC_KF).

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_GK_FC) as Par_FC_GK.
	pose proof (by_prop_Par_flip _ _ _ _ Par_FC_GK) as (Par_CF_GK & _ & _).
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_GC_KF) as TarskiPar_GC_KF.

	assert (TarskiPar_GC_KF_2 := TarskiPar_GC_KF).
	destruct TarskiPar_GC_KF_2 as (_ & neq_K_F & n_Meet_G_C_K_F & SameSide_K_F_GC).

	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_K_F_GC) as SameSide_K_F_CG.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_K_F_CG) as (SameSide_F_K_CG & _ & _).

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_EAH_EAH OnRay_AE_B OnRay_AH_D) as CongA_EAH_BAD.
	pose proof (by_prop_CongA_flip _ _ _ _ _ _ CongA_EAH_BAD) as CongA_HAE_DAB.

	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_C_D_BA Col_B_A_E neq_B_E) as SameSide_C_D_BE.
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_C_D_BE Col_B_A_E OnRay_AD_H) as SameSide_C_H_BE.
	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_H_K_EA Col_E_A_B neq_E_B) as SameSide_H_K_EB.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_H_K_EB) as SameSide_H_K_BE.
	pose proof (lemma_samesidetransitive _ _ _ _ _ SameSide_C_H_BE SameSide_H_K_BE) as SameSide_C_K_BE.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_C_K_BE) as (SameSide_K_C_BE & _ & _).
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_K_C_BE Col_B_B_E OnRay_BC_G) as SameSide_K_G_BE.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_K_G_BE) as SameSide_K_G_EB.

	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_A_D_BC Col_B_C_C OnRay_CD_F) as SameSide_A_F_BC.
	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_K_F_CG Col_C_G_B neq_C_B) as SameSide_K_F_CB.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_K_F_CB) as SameSide_K_F_BC.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_K_F_BC) as (SameSide_F_K_BC & _ & _).
	pose proof (lemma_samesidetransitive _ _ _ _ _ SameSide_A_F_BC SameSide_F_K_BC) as SameSide_A_K_BC.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_A_K_BC) as (SameSide_K_A_BC & _ & _).
	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_K_A_BC Col_B_C_G neq_B_G) as SameSide_K_A_BG.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_K_A_BG) as SameSide_K_A_GB.

	pose proof (lemma_extension _ _ _ _ neq_B_A neq_B_A) as (e & BetS_B_A_e & Cong_Ae_BA).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_e) as BetS_e_A_B.
	pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_B_E_A BetS_B_A_e) as BetS_E_A_e.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_A_e) as BetS_e_A_E.

	pose proof (proposition_29C _ _ _ _ _ Par_AD_BC SameSide_D_C_AB BetS_e_A_B) as (_ & SumTwoRT_DAB_ABC).
	pose proof (proposition_29C _ _ _ _ _ Par_AH_EK SameSide_H_K_AE BetS_e_A_E) as (_ & SumTwoRT_HAE_AEK).

	pose proof (
		lemma_supplements_SumTwoRT
		H A E A B C D A B A E K
		SumTwoRT_HAE_AEK
		CongA_HAE_DAB
		SumTwoRT_DAB_ABC
	) as (CongA_AEK_ABC & CongA_ABC_AEK).

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_AEK_ABC OnRay_BA_E OnRay_BC_G) as CongA_AEK_EBG.

	pose proof (proposition_28D _ _ _ _ _ BetS_A_E_B CongA_AEK_EBG SameSide_K_G_EB) as Par_EK_BG.
	pose proof (by_prop_Par_flip _ _ _ _ Par_EK_BG) as (_ & Par_EK_GB & _).

	pose proof (lemma_extension _ _ _ _ neq_B_C neq_B_C) as (c & BetS_B_C_c & Cong_Cc_BC).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_C_c) as BetS_c_C_B.
	pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_c_C_B BetS_C_G_B) as BetS_c_C_G.

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_C_G_B neq_C_G) as OnRay_CG_B.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_CG_B) as OnRay_CB_G.

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_DCB_DCB OnRay_CD_F OnRay_CB_G) as CongA_DCB_FCG.

	pose proof (proposition_29C _ _ _ _ _ Par_CD_BA SameSide_D_A_CB BetS_c_C_B) as (_ & SumTwoRT_DCB_CBA).
	pose proof (proposition_29C _ _ _ _ _ Par_CF_GK SameSide_F_K_CG BetS_c_C_G) as (_ & SumTwoRT_FCG_CGK).

	pose proof (
		lemma_supplements_SumTwoRT
		D C B C G K F C G C B A
		SumTwoRT_DCB_CBA
		CongA_DCB_FCG
		SumTwoRT_FCG_CGK
	) as (CongA_CBA_CGK & CongA_CGK_CBA).

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_CGK_CBA OnRay_BC_G OnRay_BA_A) as CongA_CGK_GBA.

	pose proof (proposition_28D _ _ _ _ _ BetS_C_G_B CongA_CGK_GBA SameSide_K_A_GB) as Par_GK_BA.
	pose proof (by_prop_Par_flip _ _ _ _ Par_GK_BA) as (_ & Par_GK_AB & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_GK_AB Col_A_B_E neq_E_B) as Par_GK_EB.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_GK_EB) as Par_EB_GK.
	pose proof (by_prop_Par_flip _ _ _ _ Par_EB_GK) as (_ & Par_EB_KG & _).

	pose proof (by_def_Parallelogram _ _ _ _ Par_EK_GB Par_EB_KG) as Parallelogram_E_K_G_B.

	exact Parallelogram_E_K_G_B.
Qed.

End Euclid.
