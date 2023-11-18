Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_CongTriangles.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_SameSide_flip.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_interior5.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_sameside_onray_EFAC_BFG_EGAC.
Require Import ProofCheckingEuclid.lemma_samesidecollinear.
Require Import ProofCheckingEuclid.lemma_samesidetransitive.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_23C.
Require Import ProofCheckingEuclid.proposition_42.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_42B :
	forall B C D E J K R a b c e,
	Triangle a b c ->
	Midpoint b e c ->
	nCol J D K ->
	Midpoint B E C ->
	Cong E C e c ->
	nCol R E C ->
	exists X Z, Parallelogram X E C Z /\ EqAreaQuad a b e c X E C Z /\ CongA C E X J D K /\ SameSide R X E C.
Proof.
	intros B C D E J K R a b c e.
	intros Triangle_abc.
	intros Midpoint_b_e_c.
	intros nCol_J_D_K.
	intros Midpoint_B_E_C.
	intros Cong_EC_ec.
	intros nCol_R_E_C.

	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq b b) as eq_b_b by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C b c b eq_b_b) as Col_b_c_b.
	pose proof (by_def_Col_from_eq_A_C B C B eq_B_B) as Col_B_C_B.
	pose proof (by_def_Col_from_eq_A_B B B C eq_B_B) as Col_B_B_C.
	pose proof (by_def_Col_from_eq_B_C E C C eq_C_C) as Col_E_C_C.
	pose proof (by_def_Col_from_eq_A_C C B C eq_C_C) as Col_C_B_C.

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_abc) as nCol_a_b_c.
	pose proof (by_prop_nCol_order _ _ _ nCol_a_b_c) as (nCol_b_a_c & nCol_b_c_a & nCol_c_a_b & nCol_a_c_b & nCol_c_b_a).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_a_b_c) as (neq_a_b & neq_b_c & neq_a_c & neq_b_a & neq_c_b & neq_c_a).

	destruct Midpoint_b_e_c as (BetS_b_e_c & Cong_be_ec).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_b_e_c) as BetS_c_e_b.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_b_e_c) as (neq_e_c & neq_b_e & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_c_e_b) as (neq_e_b & neq_c_e & _).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_b_e_c) as Col_b_e_c.
	pose proof (by_prop_Col_order _ _ _ Col_b_e_c) as (Col_e_b_c & Col_e_c_b & Col_c_b_e & Col_b_c_e & Col_c_e_b).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_be_ec) as (Cong_eb_ce & Cong_eb_ec & Cong_be_ce).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_be_ec) as Cong_ec_be.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_ec_be) as (Cong_ce_eb & Cong_ce_be & Cong_ec_eb).

	assert (Midpoint_B_E_C_2 := Midpoint_B_E_C).
	destruct Midpoint_B_E_C_2 as (BetS_B_E_C & Cong_BE_EC).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_E_C) as BetS_C_E_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_E_C) as (neq_E_C & neq_B_E & neq_B_C).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_E_B) as (neq_E_B & neq_C_E & neq_C_B).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_E_C) as Col_B_E_C.
	pose proof (by_prop_Col_order _ _ _ Col_B_E_C) as (Col_E_B_C & Col_E_C_B & Col_C_B_E & Col_B_C_E & Col_C_E_B).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BE_EC) as (Cong_EB_CE & Cong_EB_EC & Cong_BE_CE).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BE_EC) as Cong_EC_BE.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_EC_BE) as (Cong_CE_EB & Cong_CE_BE & Cong_EC_EB).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_EC_ec) as (Cong_CE_ce & Cong_CE_ec & Cong_EC_ce).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_EC_ec) as Cong_ec_EC.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_ec_EC) as (Cong_ce_CE & Cong_ce_EC & Cong_ec_CE).

	pose proof (by_prop_nCol_order _ _ _ nCol_R_E_C) as (nCol_E_R_C & nCol_E_C_R & nCol_C_R_E & nCol_R_C_E & nCol_C_E_R).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_E_C_R Col_E_C_B Col_E_C_C neq_B_C) as nCol_B_C_R.
	pose proof (proposition_23C _ _ _ _ _ _ neq_B_C nCol_a_b_c nCol_B_C_R) as (P & H & OnRay_BC_H & CongA_PBH_abc & SameSide_P_R_BC).

	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_BC_H) as OnRay_BH_C.

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_PBH_abc) as CongA_abc_PBH.

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_P_R_BC) as (SameSide_R_P_BC & _ & _).

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_BE_EC Cong_EC_ec) as Cong_BE_ec.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BE_ec) as (Cong_EB_ce & Cong_EB_ec & Cong_BE_ce).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BE_ec) as Cong_ec_BE.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_ec_BE) as (Cong_ce_EB & Cong_ce_BE & Cong_ec_EB).

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_BE_ec Cong_ec_be) as Cong_BE_be.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BE_be) as (Cong_EB_eb & Cong_EB_be & Cong_BE_eb).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BE_be) as Cong_be_BE.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_be_BE) as (Cong_eb_EB & Cong_eb_BE & Cong_be_EB).

	pose proof (cn_sumofparts _ _ _ _ _ _ Cong_BE_be Cong_EC_ec BetS_B_E_C BetS_b_e_c) as Cong_BC_bc.

	assert (SameSide_R_P_BC_2 := SameSide_R_P_BC).
	destruct SameSide_R_P_BC_2 as (_ & _ & _ & _ & _ & _ & _ & _ & nCol_B_C_P).
	pose proof (by_prop_nCol_order _ _ _ nCol_B_C_P) as (nCol_C_B_P & nCol_C_P_B & nCol_P_B_C & nCol_B_P_C & nCol_P_C_B).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_C_P) as (_ & neq_C_P & neq_B_P & _ & neq_P_C & neq_P_B).

	pose proof (lemma_layoff _ _ _ _ neq_B_P neq_b_a) as (A & OnRay_BP_A & Cong_BA_ba).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BA_ba) as (Cong_AB_ab & Cong_AB_ba & Cong_BA_ab).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BA_ba) as Cong_ba_BA.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_ba_BA) as (Cong_ab_AB & Cong_ab_BA & Cong_ba_AB).

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_abc_PBH OnRay_BP_A OnRay_BH_C) as CongA_abc_ABC.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_abc_ABC) as CongA_ABC_abc.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_abc_ABC) as nCol_A_B_C.
	pose proof (by_def_Triangle _ _ _ nCol_A_B_C) as Triangle_ABC.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & _ & neq_A_C & neq_B_A & _ & neq_C_A).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_C_A Col_B_C_B Col_B_C_E neq_B_E) as nCol_B_E_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_B_E_A) as (_ & _ & _ & _ & nCol_A_E_B).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_b_c_a Col_b_c_b Col_b_c_e neq_b_e) as nCol_b_e_a.
	pose proof (by_prop_nCol_order _ _ _ nCol_b_e_a) as (_ & _ & _ & _ & nCol_a_e_b).

	pose proof (proposition_04 _ _ _ _ _ _ Cong_BA_ba Cong_BC_bc CongA_ABC_abc) as (Cong_AC_ac & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AC_ac) as (Cong_CA_ca & Cong_CA_ac & Cong_AC_ca).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AC_ac) as Cong_ac_AC.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_ac_AC) as (Cong_ca_CA & Cong_ca_AC & Cong_ac_CA).

	pose proof (lemma_interior5 _ _ _ _ _ _ _ _ BetS_B_E_C BetS_b_e_c Cong_BE_be Cong_EC_ec Cong_BA_ba Cong_CA_ca) as Cong_EA_ea.

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_EA_ea) as (Cong_AE_ae & Cong_AE_ea & Cong_EA_ae).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_EA_ea) as Cong_ea_EA.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_ea_EA) as (Cong_ae_AE & Cong_ae_EA & Cong_ea_AE).

	pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_AE_ae Cong_EB_eb Cong_AB_ab) as CongTriangles_AEB_aeb.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_AEB_aeb) as EqAreaTri_AEB_aeb.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_C_B_A Col_C_B_C Col_C_B_E neq_C_E) as nCol_C_E_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_C_E_A) as (_ & _ & _ & _ & nCol_A_E_C).

	pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_AE_ae Cong_EC_ec Cong_AC_ac) as CongTriangles_AEC_aec.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_AEC_aec) as EqAreaTri_AEC_aec.

	assert (eq E E) as eq_E_E by (reflexivity).
	assert (eq e e) as eq_e_e by (reflexivity).

	assert (BetS A E E \/ eq A E \/ eq E E) as eq_E_E' by (right; right; exact eq_E_E).
	assert (BetS a e e \/ eq a e \/ eq e e) as eq_e_e' by (right; right; exact eq_e_e).

	pose proof (
		axiom_paste3
		A E B C E a e b c e
		EqAreaTri_AEB_aeb
		EqAreaTri_AEC_aec
		BetS_B_E_C
		eq_E_E'
		BetS_b_e_c
		eq_e_e'
	) as EqAreaQuad_ABEC_abec.
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_ABEC_abec) as EqAreaQuad_abec_ABEC.

	pose proof (proposition_42 _ _ _ _ _ _ _ Triangle_ABC nCol_J_D_K Midpoint_B_E_C) as (F & G & Parallelogram_F_E_C_G & EqAreaQuad_ABEC_FECG & CongA_CEF_JDK & Col_F_G_A).

	assert (Parallelogram_F_E_C_G_2 := Parallelogram_F_E_C_G).
	destruct Parallelogram_F_E_C_G_2 as (Par_FE_CG & Par_FG_EC).

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_FG_EC) as Par_EC_FG.
	pose proof (by_prop_Par_flip _ _ _ _ Par_EC_FG) as (_ & Par_EC_GF & _).

	pose proof (by_prop_Col_order _ _ _ Col_F_G_A) as (Col_G_F_A & _ & _ & _ & _).

	pose proof (axiom_EqAreaQuad_transitive _ _ _ _ _ _ _ _ _ _ _ _ EqAreaQuad_abec_ABEC EqAreaQuad_ABEC_FECG) as EqAreaQuad_abec_FECG.

	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_R_P_BC Col_B_B_C OnRay_BP_A) as SameSide_R_A_BC.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_R_A_BC) as SameSide_R_A_CB.
	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_R_A_CB Col_C_B_E neq_C_E) as SameSide_R_A_CE.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_R_A_CE) as (SameSide_A_R_CE & _ & _).
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_R_A_CE) as SameSide_R_A_EC.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_A_R_CE) as SameSide_A_R_EC.


	(* assert by cases *)
	assert (SameSide R F E C) as SameSide_R_F_EC.
	assert (eq A F \/ neq A F) as [eq_A_F|neq_A_F] by (apply Classical_Prop.classic).
	{
		(* case eq_A_F *)
		assert (SameSide R F E C) as SameSide_R_F_EC by (rewrite <- eq_A_F; exact SameSide_R_A_EC).

		exact SameSide_R_F_EC.
	}
	{
		(* case neq_A_F *)
		pose proof (by_prop_Par_collinear _ _ _ _ _ Par_EC_GF Col_G_F_A neq_A_F) as Par_EC_AF.
		pose proof (by_prop_Par_flip _ _ _ _ Par_EC_AF) as (_ & Par_EC_FA & _).
		pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_EC_FA) as TarskiPar_EC_FA.
		assert (TarskiPar_EC_FA_2 := TarskiPar_EC_FA).
		destruct TarskiPar_EC_FA_2 as (_ & neq_F_A & n_Meet_E_C_F_A & SameSide_F_A_EC).

		pose proof (lemma_samesidetransitive _ _ _ _ _ SameSide_F_A_EC SameSide_A_R_EC) as SameSide_F_R_EC.
		pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_F_R_EC) as (SameSide_R_F_EC & _ & _).

		exact SameSide_R_F_EC.
	}

	exists F, G.
	split.
	exact Parallelogram_F_E_C_G.
	split.
	exact EqAreaQuad_abec_FECG.
	split.
	exact CongA_CEF_JDK.
	exact SameSide_R_F_EC.
Qed.

End Euclid.
