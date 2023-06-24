Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence_smaller.
Require Import ProofCheckingEuclid.lemma_angletrichotomy.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalanglesflip.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_orderofpoints_any.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_onray.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_par.
Require Import ProofCheckingEuclid.lemma_s_ss.
Require Import ProofCheckingEuclid.lemma_s_supp.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.
Require Import ProofCheckingEuclid.lemma_supplements_conga.
Require Import ProofCheckingEuclid.proposition_16.


Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.



Lemma proposition_27 :
	forall A B C D E F,
	BetS A E B ->
	BetS C F D ->
	CongA A E F E F D ->
	OS A E F D ->
	Par A B C D.
Proof.
	intros A B C D E F.
	intros BetS_A_E_B.
	intros BetS_C_F_D.
	intros CongA_AEF_EFD.
	intros OS_A_EF_D.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq D D) as eq_D_D by (reflexivity).
	assert (eq E E) as eq_E_E by (reflexivity).
	assert (eq F F) as eq_F_F by (reflexivity).

	pose proof (lemma_s_col_eq_A_C A B A eq_A_A) as Col_A_B_A.
	pose proof (lemma_s_col_eq_B_C C D D eq_D_D) as Col_C_D_D.
	pose proof (lemma_s_col_eq_A_C E F E eq_E_E) as Col_E_F_E.
	pose proof (lemma_s_col_eq_B_C E F F eq_F_F) as Col_E_F_F.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_B) as BetS_B_E_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_E_B) as (_ & _ & neq_A_B).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_E_B) as (_ & neq_A_E & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_E_B) as Col_A_E_B.
	pose proof (lemma_s_col_BetS_A_C_B _ _ _ BetS_A_E_B) as Col_A_B_E.
	pose proof (lemma_collinearorder _ _ _ Col_A_E_B) as (_ & _ & Col_B_A_E & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_F_D) as BetS_D_F_C.
	pose proof (lemma_betweennotequal _ _ _ BetS_C_F_D) as (neq_F_D & _ & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_C_F_D) as (_ & _ & neq_C_D).
	pose proof (lemma_inequalitysymmetric _ _ neq_C_D) as neq_D_C.
	pose proof (lemma_inequalitysymmetric _ _ neq_F_D) as neq_D_F.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_C_F_D) as Col_C_F_D.
	pose proof (lemma_collinearorder _ _ _ Col_C_F_D) as (_ & _ & _ & Col_C_D_F & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_D_F) as (_ & Col_D_F_C & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_D_F) as (Col_D_C_F & _ & _ & _ & _).

	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_AEF_EFD) as CongA_EFD_AEF.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_AEF_EFD) as nCol_E_F_D.
	pose proof (lemma_NCorder _ _ _ nCol_E_F_D) as (nCol_F_E_D & nCol_F_D_E & nCol_D_E_F & nCol_E_D_F & nCol_D_F_E).

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_E_F_D) as CongA_EFD_DFE.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_AEF_EFD CongA_EFD_DFE) as CongA_AEF_DFE.

	pose proof (lemma_s_os _ _ _ _ _ BetS_D_F_C Col_E_F_F nCol_E_F_D) as OS_D_EF_C.

	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_EFD_AEF) as (neq_E_F & _ & _ & _ & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_E_F) as neq_F_E.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_E_F) as OnRay_EF_F.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_F_E) as OnRay_FE_E.
	pose proof (lemma_s_supp _ _ _ _ _ OnRay_EF_F BetS_A_E_B) as Supp_AEF_FEB.
	pose proof (lemma_s_supp _ _ _ _ _ OnRay_FE_E BetS_D_F_C) as Supp_DFE_EFC.
	pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_AEF_DFE Supp_AEF_FEB Supp_DFE_EFC) as CongA_FEB_EFC.
	pose proof (lemma_equalanglesflip _ _ _ _ _ _ CongA_FEB_EFC) as CongA_BEF_CFE.

	assert (OS_A_EF_D2 := OS_A_EF_D).
	destruct OS_A_EF_D2 as (H & BetS_A_H_D & Col_E_F_H & nCol_E_F_A).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_H_D) as BetS_D_H_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_H_D) as (_ & _ & neq_A_D).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_H_D) as (neq_H_D & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_D) as neq_D_A.
	pose proof (lemma_inequalitysymmetric _ _ neq_H_D) as neq_D_H.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_H_D) as Col_A_H_D.
	pose proof (lemma_collinearorder _ _ _ Col_A_H_D) as (_ & _ & _ & _ & Col_D_H_A).
	pose proof (lemma_collinearorder _ _ _ Col_A_H_D) as (_ & _ & Col_D_A_H & _ & _).

	pose proof (lemma_collinearorder _ _ _ Col_E_F_H) as (Col_F_E_H & Col_F_H_E & Col_H_E_F & Col_E_H_F & Col_H_F_E).

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_E_F_A) as n_Col_E_F_A.
	pose proof (lemma_NCorder _ _ _ nCol_E_F_A) as (nCol_F_E_A & nCol_F_A_E & nCol_A_E_F & nCol_E_A_F & nCol_A_F_E).
	pose proof (lemma_equalanglesreflexive _ _ _ nCol_F_E_A) as CongA_FEA_FEA.
	pose proof (lemma_s_triangle _ _ _ nCol_E_A_F) as Triangle_EAF.


	assert (~ Meet A B C D) as n_Meet_A_B_C_D.
	{
		intro Meet_A_B_C_D.

		assert (Meet_A_B_C_D2 := Meet_A_B_C_D).
		destruct Meet_A_B_C_D2 as (G & _ & _ & Col_A_B_G & Col_C_D_G).

		pose proof (lemma_collinearorder _ _ _ Col_A_B_G) as (Col_B_A_G & _ & _ & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_G Col_B_A_E neq_B_A) as Col_A_G_E.
		pose proof (lemma_collinearorder _ _ _ Col_A_G_E) as (Col_G_A_E & Col_G_E_A & Col_E_A_G & Col_A_E_G & Col_E_G_A).

		pose proof (lemma_collinearorder _ _ _ Col_C_D_G) as (_ & _ & _ & Col_C_G_D & _).
		pose proof (lemma_collinearorder _ _ _ Col_C_G_D) as (Col_G_C_D & _ & _ & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_D_G Col_C_D_F neq_C_D) as Col_D_G_F.
		pose proof (lemma_collinearorder _ _ _ Col_D_G_F) as (_ & Col_G_F_D & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_D_G_F) as (Col_G_D_F & _ & _ & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_D_F Col_C_D_G neq_C_D) as Col_D_F_G.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_F_G Col_D_F_C neq_D_F) as Col_F_G_C.
		pose proof (lemma_collinearorder _ _ _ Col_F_G_C) as (Col_G_F_C & Col_G_C_F & Col_C_F_G & Col_F_C_G & Col_C_G_F).


		assert (~ BetS A E G) as n_BetS_A_E_G.
		{
			intro BetS_A_E_G.

			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_G) as BetS_G_E_A.
			pose proof (lemma_betweennotequal _ _ _ BetS_A_E_G) as (neq_E_G & _ & neq_A_G).
			pose proof (lemma_betweennotequal _ _ _ BetS_G_E_A) as (neq_E_A & neq_G_E & neq_G_A).

			pose proof (lemma_s_onray _ _ _ _ BetS_A_E_G BetS_A_E_B) as OnRay_EG_B.

			pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_E_F Col_A_E_G neq_A_G) as nCol_A_G_F.
			pose proof (lemma_NCdistinct _ _ _ nCol_A_G_F) as (_ & neq_G_F & neq_A_F & _ & neq_F_G & neq_F_A).
			pose proof (lemma_NCorder _ _ _ nCol_A_G_F) as (nCol_G_A_F & nCol_G_F_A & nCol_F_A_G & nCol_A_F_G & nCol_F_G_A).

			pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_G_A_F Col_G_A_E neq_G_E) as nCol_G_E_F.
			pose proof (lemma_NCorder _ _ _ nCol_G_E_F) as (nCol_E_G_F & nCol_E_F_G & nCol_F_G_E & nCol_G_F_E & nCol_F_E_G).

			pose proof (lemma_s_triangle _ _ _ nCol_E_G_F) as Triangle_EGF.
			pose proof (lemma_equalanglesreflexive _ _ _ nCol_G_E_F) as CongA_GEF_GEF.
			pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_GEF_GEF OnRay_EG_B OnRay_EF_F) as CongA_GEF_BEF.
			pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_GEF_BEF) as nCol_B_E_F.

			pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_E_F) as CongA_BEF_FEB.
			pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_GEF_BEF CongA_BEF_FEB) as CongA_GEF_FEB.
			pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_GEF_FEB) as CongA_FEB_GEF.

			pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_E_F_H Col_E_F_E BetS_D_H_A BetS_G_E_A nCol_E_F_D nCol_E_F_G) as SS_D_G_EF.
			pose proof (lemma_samesidesymmetric _ _ _ _ SS_D_G_EF) as (SS_G_D_EF & _ & _).
			pose proof (lemma_planeseparation _ _ _ _ _ SS_G_D_EF OS_D_EF_C) as OS_G_EF_C.

			destruct OS_G_EF_C as (R & BetS_G_R_C & Col_E_F_R & _).

			pose proof (lemma_betweennotequal _ _ _ BetS_G_R_C) as (_ & _ & neq_G_C).
			pose proof (lemma_inequalitysymmetric _ _ neq_G_C) as neq_C_G.
			pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_G_R_C) as Col_G_R_C.
			pose proof (lemma_collinearorder _ _ _ Col_G_R_C) as (Col_R_G_C & Col_R_C_G & Col_C_G_R & Col_G_C_R & Col_C_R_G).

			pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_C_G Col_C_G_R Col_C_G_F Col_C_G_D) as Col_R_F_D.
			pose proof (lemma_collinearorder _ _ _ Col_R_F_D) as (Col_F_R_D & Col_F_D_R & Col_D_R_F & Col_R_D_F & Col_D_F_R).

			pose proof (lemma_collinearorder _ _ _ Col_E_F_R) as (Col_F_E_R & Col_F_R_E & Col_R_E_F & Col_E_R_F & Col_R_F_E).

			pose proof (lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB _ _ _ _ Col_F_R_D Col_F_R_E nCol_F_D_E) as eq_F_R.

			assert (BetS G F C) as BetS_G_F_C by (rewrite eq_F_R; exact BetS_G_R_C).

			pose proof (proposition_16 _ _ _ _ Triangle_EGF BetS_G_F_C) as (LtA_GEF_EFC & _).
			pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_GEF_EFC CongA_FEB_EFC) as LtA_GEF_FEB.
			pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_GEF_FEB CongA_FEB_GEF) as LtA_FEB_FEB.
			pose proof (lemma_angletrichotomy _ _ _ _ _ _ LtA_FEB_FEB) as n_LtA_FEB_FEB.

			contradict LtA_FEB_FEB.
			exact n_LtA_FEB_FEB.
		}

		assert (~ OnRay E A G) as n_OnRay_EA_G.
		{
			intro OnRay_EA_G.

			pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_EA_G) as OnRay_EG_A.
			pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_EFD_AEF OnRay_EA_G OnRay_EF_F) as CongA_EFD_GEF.

			pose proof (lemma_onray_strict _ _ _ OnRay_EA_G) as neq_E_G.
			pose proof (lemma_onray_strict _ _ _ OnRay_EG_A) as neq_E_A.
			pose proof (lemma_inequalitysymmetric _ _ neq_E_G) as neq_G_E.

			pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_E_A_F Col_E_A_G neq_E_G) as nCol_E_G_F.
			pose proof (lemma_NCorder _ _ _ nCol_E_G_F) as (nCol_G_E_F & nCol_G_F_E & nCol_F_E_G & nCol_E_F_G & nCol_F_G_E).

			pose proof (lemma_s_triangle _ _ _ nCol_E_G_F) as Triangle_EGF.

			(* assert by cases *)
			assert (BetS B E G) as BetS_B_E_G.
			pose proof (lemma_onray_orderofpoints_any _ _ _ OnRay_EA_G) as [BetS_E_G_A | [eq_A_G | BetS_E_A_G]].
			{
				(* case BetS_E_G_A *)
				pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_B_E_A BetS_E_G_A) as BetS_B_E_G.

				exact BetS_B_E_G.
			}
			{
				(* case eq_A_G *)
				pose proof (lemma_equalitysymmetric _ _ eq_A_G) as eq_G_A.
				assert (BetS B E G) as BetS_B_E_G by (rewrite eq_G_A; exact BetS_B_E_A).

				exact BetS_B_E_G.
			}
			{
				(* case BetS_E_A_G *)
				pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_B_E_A BetS_E_A_G) as BetS_B_E_G.

				exact BetS_B_E_G.
			}
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_E_G) as BetS_G_E_B.

			pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_E_F_E Col_E_F_E BetS_A_E_B BetS_G_E_B nCol_E_F_A nCol_E_F_G) as SS_A_G_EF.
			pose proof (lemma_samesidesymmetric _ _ _ _ SS_A_G_EF) as (SS_G_A_EF & _ & _).
			pose proof (lemma_planeseparation _ _ _ _ _ SS_G_A_EF OS_A_EF_D) as OS_G_EF_D.

			destruct OS_G_EF_D as (P & BetS_G_P_D & Col_E_F_P & _).

			pose proof (lemma_betweennotequal _ _ _ BetS_G_P_D) as (_ & _ & neq_G_D).

			pose proof (lemma_collinearorder _ _ _ Col_E_F_P) as (Col_F_E_P & Col_F_P_E & Col_P_E_F & Col_E_P_F & Col_P_F_E).

			pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_G_P_D) as Col_G_P_D.
			pose proof (lemma_collinearorder _ _ _ Col_G_P_D) as (_ & _ & _ & Col_G_D_P & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_D_P Col_G_D_F neq_G_D) as Col_D_P_F.
			pose proof (lemma_collinearorder _ _ _ Col_D_P_F) as (Col_P_D_F & Col_P_F_D & Col_F_D_P & Col_D_F_P & Col_F_P_D).

			pose proof (lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB _ _ _ _ Col_F_P_D Col_F_P_E nCol_F_D_E) as eq_F_P.
			pose proof (lemma_equalitysymmetric _ _ eq_F_P) as eq_P_F.

			assert (BetS G F D) as BetS_G_F_D by (rewrite <- eq_P_F; exact BetS_G_P_D).

			pose proof (proposition_16 _ _ _ _ Triangle_EGF BetS_G_F_D) as (LtA_GEF_EFD & _).
			pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_GEF_EFD CongA_EFD_GEF) as LtA_EFD_EFD.
			pose proof (lemma_angletrichotomy _ _ _ _ _ _ LtA_EFD_EFD) as n_LtA_EFD_EFD.

			contradict LtA_EFD_EFD.
			exact n_LtA_EFD_EFD.
		}


		(* assert by cases *)
		assert (~ Meet A B C D) as n_Meet_A_B_C_D.
		destruct Col_A_E_G as [eq_A_E | [eq_A_G | [eq_E_G | [BetS_E_A_G | [BetS_A_E_G | BetS_A_G_E]]]]].
		{
			(* case eq_A_E *)

			contradict eq_A_E.
			exact neq_A_E.
		}
		{
			(* case eq_A_G *)
			assert (Col D A F) as Col_D_A_F by (rewrite eq_A_G; exact Col_D_G_F).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_A_F Col_D_A_H neq_D_A) as Col_A_F_H.
			pose proof (lemma_collinearorder _ _ _ Col_A_F_H) as (Col_F_A_H & Col_F_H_A & Col_H_A_F & Col_A_H_F & Col_H_F_A).

			pose proof (lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB _ _ _ _ Col_F_H_A Col_F_H_E nCol_F_A_E) as eq_F_H.
			pose proof (lemma_equalitysymmetric _ _ eq_F_H) as eq_H_F.

			assert (BetS A F D) as BetS_A_F_D by (rewrite <- eq_H_F; exact BetS_A_H_D).

			pose proof (proposition_16 _ _ _ _ Triangle_EAF BetS_A_F_D) as (LtA_AEF_EFD & _).
			pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_AEF_EFD CongA_EFD_AEF) as LtA_EFD_EFD.
			pose proof (lemma_angletrichotomy _ _ _ _ _ _ LtA_EFD_EFD) as n_LtA_EFD_EFD.

			contradict LtA_EFD_EFD.
			exact n_LtA_EFD_EFD.
		}
		{
			(* case eq_E_G *)
			assert (Col C D E) as Col_C_D_E by (rewrite eq_E_G; exact Col_C_D_G).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_D_E Col_C_D_F neq_C_D) as Col_D_E_F.
			pose proof (lemma_collinearorder _ _ _ Col_D_E_F) as (_ & Col_E_F_D & _ & _ & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_F_D Col_E_F_H neq_E_F) as Col_F_D_H.
			pose proof (lemma_collinearorder _ _ _ Col_F_D_H) as (_ & Col_D_H_F & _ & _ & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_H_F Col_D_H_A neq_D_H) as Col_H_F_A.
			pose proof (lemma_collinearorder _ _ _ Col_H_F_A) as (Col_F_H_A & Col_F_A_H & Col_A_H_F & Col_H_A_F & Col_A_F_H).

			pose proof (lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB _ _ _ _ Col_F_H_A Col_F_H_E nCol_F_A_E) as eq_F_H.
			pose proof (lemma_equalitysymmetric _ _ eq_F_H) as eq_H_F.

			assert (Col A F D) as Col_A_F_D by (rewrite <-eq_H_F; exact Col_A_H_D).

			pose proof (lemma_collinearorder _ _ _ Col_A_F_D) as (_ & _ & _ & _ & Col_D_F_A).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_F_A Col_D_F_C neq_D_F) as Col_F_A_C.
			pose proof (lemma_collinearorder _ _ _ Col_F_A_C) as (Col_A_F_C & Col_A_C_F & Col_C_F_A & Col_F_C_A & Col_C_A_F).

			assert (nCol F A G) as nCol_F_A_G by (rewrite <- eq_E_G; exact nCol_F_A_E).

			pose proof (lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB _ _ _ _ Col_F_C_A Col_F_C_G nCol_F_A_G) as eq_F_C.
			pose proof (lemma_equalitysymmetric _ _ eq_F_C) as eq_C_F.

			assert (Col A C D) as Col_A_C_D by (rewrite eq_C_F; exact Col_A_F_D).
			pose proof (lemma_collinearorder _ _ _ Col_A_C_D) as (_ & Col_C_D_A & _ & _ & _).
			assert (Col F D A) as Col_F_D_A by (rewrite <- eq_C_F; exact Col_C_D_A).
			assert (Col F D E) as Col_F_D_E by (rewrite <- eq_C_F; exact Col_C_D_E).
			pose proof (lemma_collinearorder _ _ _ Col_F_D_E) as (Col_D_F_E & _ & _ & _ & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_F_E Col_D_F_A neq_D_F) as Col_F_E_A.
			pose proof (lemma_collinearorder _ _ _ Col_F_E_A) as (Col_E_F_A & _ & _ & _ & _).

			contradict Col_E_F_A.
			exact n_Col_E_F_A.
		}
		{
			(* case BetS_E_A_G *)
			pose proof (lemma_betweennotequal _ _ _ BetS_E_A_G) as (_ & neq_E_A & _).

			pose proof (lemma_s_onray_assert_bets_ABE _ _ _ BetS_E_A_G neq_E_A) as OnRay_EA_G.

			contradict OnRay_EA_G.
			exact n_OnRay_EA_G.
		}
		{
			(* case BetS_A_E_G *)
			contradict BetS_A_E_G.
			exact n_BetS_A_E_G.
		}
		{
			(* case BetS_A_G_E *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_G_E) as BetS_E_G_A.
			pose proof (lemma_betweennotequal _ _ _ BetS_E_G_A) as (_ & _ & neq_E_A).

			pose proof (lemma_s_onray_assert_bets_AEB _ _ _ BetS_E_G_A neq_E_A) as OnRay_EA_G.

			contradict OnRay_EA_G.
			exact n_OnRay_EA_G.
		}

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_A_E_B Col_C_F_D neq_A_B neq_C_D neq_A_E neq_F_D n_Meet_A_B_C_D BetS_A_H_D Col_E_F_H) as BetS_E_H_F.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_H_F) as BetS_F_H_E.

	pose proof (lemma_s_par _ _ _ _ _ _ _ _ _ neq_A_B neq_C_D Col_A_B_A Col_A_B_E neq_A_E Col_C_D_F Col_C_D_D neq_F_D n_Meet_A_B_C_D BetS_A_H_D BetS_F_H_E) as Par_A_B_C_D.

	exact Par_A_B_C_D.
Qed.

End Euclid.
