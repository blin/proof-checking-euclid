Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_collinearright.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_droppedperpendicularunique.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_extensionunique.
Require Import ProofCheckingEuclid.lemma_fiveline.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_interior5.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_right_triangle_NC.
Require Import ProofCheckingEuclid.lemma_right_triangle_leg_change.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
Require Import ProofCheckingEuclid.lemma_s_onray.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_right_triangle.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.
Require Import ProofCheckingEuclid.proposition_12.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_07 :
	forall A B C D,
	neq A B ->
	Cong C A D A ->
	Cong C B D B ->
	SS C D A B ->
	eq C D.
Proof.
	intros A B C D.
	intros neq_A_B.
	intros Cong_CA_DA.
	intros Cong_CB_DB.
	intros SS_C_D_AB.

	pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_CA_DA) as (Cong_AC_AD & _ & _).
	pose proof (lemma_doublereverse _ _ _ _ Cong_CB_DB) as (Cong_BD_BC & Cong_BC_BD).

	pose proof (lemma_samesidesymmetric _ _ _ _ SS_C_D_AB) as (SS_D_C_AB & _ & _).
	destruct SS_C_D_AB as (_ & _ & _ & _ & _ & _ & _ & nCol_A_B_C & _).

	pose proof (proposition_12 _ _ _ nCol_A_B_C) as (F & Perp_at_CF_AB_F).
	destruct Perp_at_CF_AB_F as (H & _ & Col_A_B_F & Col_A_B_H & RightTriangle_HFC).

	pose proof (lemma_collinearorder _ _ _ Col_A_B_F) as (Col_B_A_F & _ & _ & Col_A_F_B & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_H) as (Col_B_A_H & _ & _ & _ & _).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_F Col_B_A_H neq_B_A) as Col_A_F_H.
	pose proof (lemma_collinearorder _ _ _ Col_A_F_H) as (_ & _ & _ & _ & Col_H_F_A).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_F Col_A_B_H neq_A_B) as Col_B_F_H.
	pose proof (lemma_collinearorder _ _ _ Col_B_F_H) as (_ & _ & _ & _ & Col_H_F_B).

	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_HFC) as nCol_H_F_C.
	pose proof (lemma_NCdistinct _ _ _ nCol_H_F_C) as (_ & neq_F_C & _ & _ & neq_C_F & _).
	pose proof (lemma_extension _ _ _ _ neq_C_F neq_F_C) as (E & BetS_C_F_E & Cong_FE_FC).

	pose proof (lemma_congruenceflip _ _ _ _ Cong_FE_FC) as (_ & _ & Cong_FE_CF).
	pose proof (lemma_doublereverse _ _ _ _ Cong_FE_FC) as (_ & Cong_EF_CF).

	pose proof (lemma_s_os _ _ _ _ _ BetS_C_F_E Col_A_B_F nCol_A_B_C) as OS_C_AB_E.
	pose proof (lemma_planeseparation _ _ _ _ _ SS_D_C_AB OS_C_AB_E) as OS_D_AB_E.
	destruct OS_D_AB_E as (G & BetS_D_G_E & Col_A_B_G & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_G) as (Col_B_A_G & _ & _ & _ & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_G Col_A_B_F neq_A_B) as Col_B_G_F.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_F Col_B_A_G neq_B_A) as Col_A_F_G.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_F_E) as BetS_E_F_C.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_G_E) as BetS_E_G_D.

	pose proof (lemma_extension _ _ _ _ neq_A_B neq_B_A) as (K & BetS_A_B_K & Cong_BK_BA).
	pose proof (lemma_extension _ _ _ _ neq_B_A neq_A_B) as (J & BetS_B_A_J & Cong_AJ_AB).
	pose proof (lemma_s_onray_assert_bets_ABE _ _ _ BetS_A_B_K neq_A_B) as OnRay_AB_K.
	pose proof (lemma_s_onray_assert_bets_ABE _ _ _ BetS_B_A_J neq_B_A) as OnRay_BA_J.
	assert (Col A B J) as Col_A_B_J by (unfold Col; one_of_disjunct BetS_B_A_J).
	assert (Col B A K) as Col_B_A_K by (unfold Col; one_of_disjunct BetS_A_B_K).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_J) as (Col_B_A_J & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_B_A_J) as (_ & _ & _ & _ & Col_J_A_B).
	pose proof (lemma_collinearorder _ _ _ Col_B_A_K) as (Col_A_B_K & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_K) as (_ & _ & _ & _ & Col_K_B_A).

	pose proof (lemma_betweennotequal _ _ _ BetS_B_A_J) as (neq_A_J & _ & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_K) as (neq_B_K & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_J) as neq_J_A.
	pose proof (lemma_inequalitysymmetric _ _ neq_B_K) as neq_K_B.

	pose proof (cn_congruencereflexive A B) as Cong_AB_AB.
	pose proof (cn_congruencereflexive A F) as Cong_AF_AF.
	pose proof (cn_congruencereflexive A G) as Cong_AG_AG.
	pose proof (cn_congruencereflexive B A) as Cong_BA_BA.
	pose proof (cn_congruencereflexive B F) as Cong_BF_BF.
	pose proof (cn_congruencereflexive B G) as Cong_BG_BG.
	pose proof (cn_congruencereflexive F B) as Cong_FB_FB.
	pose proof (cn_congruencereflexive G B) as Cong_GB_GB.

	assert (Cong A C A E) as Cong_AC_AE.
	assert (eq A F \/ neq A F) as [eq_A_F|neq_A_F] by (apply Classical_Prop.classic).
	{
		(* case eq_A_F *)
		assert (Cong A E A C) as Cong_AE_AC by (rewrite eq_A_F; exact Cong_FE_FC).
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AE_AC) as Cong_AC_AE.

		exact Cong_AC_AE.
	}
	{
		(* case neq_A_F *)
		pose proof (lemma_collinearright _ _ _ _ RightTriangle_HFC Col_H_F_A neq_A_F) as RightTriangle_AFC.
		pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_AFC) as RightTriangle_CFA.
		destruct RightTriangle_CFA as (P & BetS_C_F_P & Cong_CF_PF & Cong_CA_PA & _).

		pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_FE_CF Cong_CF_PF) as Cong_FE_PF.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_FE_PF) as (_ & _ & Cong_FE_FP).
		pose proof (lemma_extensionunique _ _ _ _ BetS_C_F_E BetS_C_F_P Cong_FE_FP) as eq_E_P.
		assert (Cong C A E A) as Cong_CA_EA by (rewrite eq_E_P; exact Cong_CA_PA).
		pose proof (lemma_congruenceflip _ _ _ _ Cong_CA_EA) as (Cong_AC_AE & _ & _).

		exact Cong_AC_AE.
	}
	(* asserted Cong_AC_AE *)

	pose proof (lemma_doublereverse _ _ _ _ Cong_AC_AE) as (Cong_EA_CA & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_EA_CA) as (_ & Cong_AE_CA & _ ).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_EA_CA) as (Cong_AE_AC & _ & _).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_AE_CA Cong_CA_DA) as Cong_AE_DA.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AE_DA) as (_ & _ & Cong_AE_AD).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AE_AD) as Cong_AD_AE.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AD_AE) as (Cong_DA_EA & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AE_AD) as (Cong_EA_DA & _ & _).

	assert (Cong B C B E) as Cong_BC_BE.
	assert (eq B F \/ neq B F) as [eq_B_F|neq_B_F] by (apply Classical_Prop.classic).
	{
		(* case eq_B_F *)
		assert (Cong B E B C) as Cong_BE_BC by (rewrite eq_B_F; exact Cong_FE_FC).
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BE_BC) as Cong_BC_BE.

		exact Cong_BC_BE.
	}
	{
		(* case neq_B_F *)
		pose proof (lemma_collinearright _ _ _ _ RightTriangle_HFC Col_H_F_B neq_B_F) as RightTriangle_BFC.
		pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_BFC) as RightTriangle_CFB.
		destruct RightTriangle_CFB as (P & BetS_C_F_P & Cong_CF_PF & Cong_CB_PB & neq_F_B).

		pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_FE_CF Cong_CF_PF) as Cong_FE_PF.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_FE_PF) as (_ & _ & Cong_FE_FP).
		pose proof (lemma_extensionunique _ _ _ _ BetS_C_F_E BetS_C_F_P Cong_FE_FP) as eq_E_P.
		assert (Cong C B E B) as Cong_CB_EB by (rewrite eq_E_P; exact Cong_CB_PB).
		pose proof (lemma_congruenceflip _ _ _ _ Cong_CB_EB) as (Cong_BC_BE & _ & _).

		exact Cong_BC_BE.
	}
	(* asserted Cong_BC_BE *)

	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_BD_BC Cong_BC_BE) as Cong_BD_BE.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_BD_BE) as (Cong_DB_EB & _ & _).
	pose proof (lemma_doublereverse _ _ _ _ Cong_BC_BE) as (Cong_EB_CB & _).
	pose proof (lemma_doublereverse _ _ _ _ Cong_BD_BE) as (Cong_EB_DB & _).

	assert (Cong G D G E) as Cong_GD_GE.
	destruct Col_A_B_G as [eq_A_B | [eq_A_G | [eq_B_G | [BetS_B_A_G | [BetS_A_B_G | BetS_A_G_B]]]]].
	{
		(* case eq_A_B *)
		contradict eq_A_B.
		exact neq_A_B.
	}
	{
		(* case eq_A_G *)
		assert (Cong G D G E) as Cong_GD_GE by (rewrite <- eq_A_G; exact Cong_AD_AE).
		exact Cong_GD_GE.
	}
	{
		(* case eq_B_G *)
		assert (Cong G D G E) as Cong_GD_GE by (rewrite <- eq_B_G; exact Cong_BD_BE).
		exact Cong_GD_GE.
	}
	{
		(* case BetS_B_A_G *)
		pose proof (
			axiom_5_line
			_ _ _ _
			_ _ _ _
			Cong_BA_BA
			Cong_AD_AE
			Cong_DB_EB
			BetS_B_A_G
			BetS_B_A_G
			Cong_DA_EA
			Cong_AG_AG
		) as Cong_GD_GE.
		exact Cong_GD_GE.
	}
	{
		(* case BetS_A_B_G *)
		pose proof (
			axiom_5_line
			_ _ _ _
			_ _ _ _
			Cong_AB_AB
			Cong_BD_BE
			Cong_DA_EA
			BetS_A_B_G
			BetS_A_B_G
			Cong_DB_EB
			Cong_BG_BG
		) as Cong_GD_GE.
		exact Cong_GD_GE.
	}
	{
		(* case BetS_A_G_B *)
		pose proof (
			lemma_interior5
			_ _ _ _
			_ _ _ _
			BetS_A_G_B
			BetS_A_G_B
			Cong_AG_AG
			Cong_GB_GB
			Cong_AD_AE
			Cong_BD_BE
		) as Cong_GD_GE.
		exact Cong_GD_GE.
	}
	(* asserted Cong_GD_GE *)

	pose proof (lemma_doublereverse _ _ _ _ Cong_GD_GE) as (Cong_EG_DG & _).

	assert (eq F G) as eq_F_G.
	assert (eq A G \/ neq A G) as [eq_A_G|neq_A_G] by (apply Classical_Prop.classic).
	{
		(* case eq_A_G *)
		assert (neq G B) as neq_G_B by (rewrite <- eq_A_G; exact neq_A_B).
		assert (BetS E A D) as BetS_E_A_D by (rewrite eq_A_G; exact BetS_E_G_D).

		pose proof (lemma_s_right_triangle _ _ _ _ BetS_E_G_D Cong_EG_DG Cong_EB_DB neq_G_B) as RightTriangle_EGB.
		pose proof (lemma_s_right_triangle _ _ _ _ BetS_E_A_D Cong_EA_DA Cong_EB_DB neq_A_B) as RightTriangle_EAB.
		pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_EAB) as RightTriangle_BAE.
		pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_EGB) as RightTriangle_BGE.

		pose proof (lemma_collinearright _ _ _ _ RightTriangle_BAE Col_B_A_J neq_J_A) as RightTriangle_JAE.

		assert (~ eq F B) as neq_F_B.
		{
			intros eq_F_B.

			assert (BetS E B C) as BetS_E_B_C by (rewrite <- eq_F_B; exact BetS_E_F_C).
			pose proof (lemma_s_right_triangle _ _ _ _ BetS_E_B_C Cong_EB_CB Cong_EA_CA neq_B_A) as RightTriangle_EBA.
			pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_EBA OnRay_BA_J) as RightTriangle_EBJ.
			pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_EBJ) as RightTriangle_JBE.
			pose proof (lemma_droppedperpendicularunique _ _ _ _ RightTriangle_JAE RightTriangle_JBE Col_J_A_B) as eq_A_B.

			contradict eq_A_B.
			exact neq_A_B.
		}

		pose proof (lemma_s_right_triangle _ _ _ _ BetS_E_F_C Cong_EF_CF Cong_EB_CB neq_F_B) as RightTriangle_EFB.
		pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_EFB) as RightTriangle_BFE.
		pose proof (lemma_droppedperpendicularunique _ _ _ _ RightTriangle_BGE RightTriangle_BFE Col_B_G_F) as eq_G_F.
		pose proof (lemma_equalitysymmetric _ _ eq_G_F) as eq_F_G.

		exact eq_F_G.
	}
	{
		(* case neq_A_G *)
		pose proof (lemma_inequalitysymmetric _ _ neq_A_G) as neq_G_A.
		pose proof (lemma_s_right_triangle _ _ _ _ BetS_E_G_D Cong_EG_DG Cong_EA_DA neq_G_A) as RightTriangle_EGA.
		pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_EGA) as RightTriangle_AGE.

		assert (eq A F \/ neq A F) as [eq_A_F|neq_A_F] by (apply Classical_Prop.classic).
		{
			(* case eq_A_F *)
			assert (neq F B) as neq_F_B by (rewrite <- eq_A_F; exact neq_A_B).
			assert (BetS E A C) as BetS_E_A_C by (rewrite eq_A_F; exact BetS_E_F_C).
			pose proof (lemma_s_right_triangle _ _ _ _ BetS_E_F_C Cong_EF_CF Cong_EB_CB neq_F_B) as RightTriangle_EFB.
			pose proof (lemma_s_right_triangle _ _ _ _ BetS_E_A_C Cong_EA_CA Cong_EB_CB neq_A_B) as RightTriangle_EAB.
			pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_EAB OnRay_AB_K) as RightTriangle_EAK.
			pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_EFB) as RightTriangle_BFE.
			pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_EAB) as RightTriangle_BAE.
			pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_EAK) as RightTriangle_KAE.

			assert (~ eq B G) as neq_B_G.
			{
				intros eq_B_G.

				assert (BetS E B D) as BetS_E_B_D by (rewrite eq_B_G; exact BetS_E_G_D).
				pose proof (lemma_s_right_triangle _ _ _ _ BetS_E_B_D Cong_EB_DB Cong_EA_DA neq_B_A) as RightTriangle_EBA.
				pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_EBA) as RightTriangle_ABE.
				pose proof (lemma_collinearright _ _ _ _ RightTriangle_ABE Col_A_B_K neq_K_B) as RightTriangle_KBE.

				pose proof (lemma_droppedperpendicularunique _ _ _ _ RightTriangle_KBE RightTriangle_KAE Col_K_B_A) as eq_B_A.

				contradict eq_B_A.
				exact neq_B_A.
			}

			pose proof (lemma_inequalitysymmetric _ _ neq_B_G) as neq_G_B.
			pose proof (lemma_s_right_triangle _ _ _ _ BetS_E_G_D Cong_EG_DG Cong_EB_DB neq_G_B) as RightTriangle_EGB.
			pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_EGB) as RightTriangle_BGE.
			pose proof (lemma_droppedperpendicularunique _ _ _ _ RightTriangle_BGE RightTriangle_BFE Col_B_G_F) as eq_G_F.
			pose proof (lemma_equalitysymmetric _ _ eq_G_F) as eq_F_G.

			exact eq_F_G.
		}
		{
			(* case neq_A_F *)
			pose proof (lemma_inequalitysymmetric _ _ neq_A_F) as neq_F_A.
			pose proof (lemma_s_right_triangle _ _ _ _ BetS_E_F_C Cong_EF_CF Cong_EA_CA neq_F_A) as RightTriangle_EFA.
			pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_EFA) as RightTriangle_AFE.
			pose proof (lemma_droppedperpendicularunique _ _ _ _ RightTriangle_AFE RightTriangle_AGE Col_A_F_G) as eq_F_G.

			exact eq_F_G.
		}
	}

	assert (Cong A F A G) as Cong_AF_AG by (rewrite <- eq_F_G; exact Cong_AF_AF).
	assert (Cong B F B G) as Cong_BF_BG by (rewrite <- eq_F_G; exact Cong_BF_BF).
	assert (Cong F B G B) as Cong_FB_GB by (rewrite <- eq_F_G; exact Cong_FB_FB).

	assert (BetS E F D) as BetS_E_F_D by (rewrite eq_F_G; exact BetS_E_G_D).
	pose proof (lemma_s_onray _ _ _ _ BetS_E_F_D BetS_E_F_C) as OnRay_FD_C.
	pose proof (lemma_betweennotequal _ _ _ BetS_E_F_D) as (neq_F_D & _ & _).
	pose proof (lemma_s_onray_assert_ABB _ _ neq_F_D) as OnRay_FD_D.

	pose proof (
		lemma_fiveline
		_ _ _ _
		_ _ _ _
		Col_A_F_B
		Cong_AF_AG
		Cong_FB_GB
		Cong_AC_AD
		Cong_BC_BD
		Cong_AB_AB
		neq_A_B
	) as Cong_FC_GD.
	assert (Cong F C F D) as Cong_FC_FD by (setoid_rewrite eq_F_G at 2; exact Cong_FC_GD).

	pose proof (lemma_layoffunique _ _ _ _ OnRay_FD_C OnRay_FD_D Cong_FC_FD) as eq_C_D.

	exact eq_C_D.
Qed.

End Euclid.
