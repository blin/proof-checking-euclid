Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NChelper.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence_smaller.
Require Import ProofCheckingEuclid.lemma_angletrichotomy_n_CongA_ABC_DEF_n_LtA_DEF_ABC_LtA_ABC_DEF.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_crossbar_LtA.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_oppositesidesymmetric.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_meet.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_ss.
Require Import ProofCheckingEuclid.lemma_s_sumtwort.
Require Import ProofCheckingEuclid.lemma_s_supp.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.
Require Import ProofCheckingEuclid.lemma_supplement_symmetric.
Require Import ProofCheckingEuclid.lemma_supplementinequality.
Require Import ProofCheckingEuclid.lemma_supplements_conga.
Require Import ProofCheckingEuclid.proposition_15a.
Require Import ProofCheckingEuclid.proposition_31.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_29 :
	forall A B C D E G H,
	Par A B C D ->
	BetS A G B ->
	BetS C H D ->
	BetS E G H ->
	OS A G H D ->
	CongA A G H G H D /\ CongA E G B G H D /\ SumTwoRT B G H G H D.
Proof.
	intros A B C D E G H.
	intros Par_A_B_C_D.
	intros BetS_A_G_B.
	intros BetS_C_H_D.
	intros BetS_E_G_H.
	intros OS_A_GH_D.

	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq G G) as eq_G_G by (reflexivity).
	assert (eq H H) as eq_H_H by (reflexivity).

	pose proof (lemma_s_col_eq_A_C C H C eq_C_C) as Col_C_H_C.
	pose proof (lemma_s_col_eq_A_C G H G eq_G_G) as Col_G_H_G.
	pose proof (lemma_s_col_eq_B_C D H H eq_H_H) as Col_D_H_H.

	destruct Par_A_B_C_D as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_A_B_C_D & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_G_B) as BetS_B_G_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_G_B) as (neq_G_B & neq_A_G & neq_A_B).
	pose proof (lemma_betweennotequal _ _ _ BetS_B_G_A) as (neq_G_A & neq_B_G & neq_B_A).

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_G_B) as Col_A_G_B.
	pose proof (lemma_collinearorder _ _ _ Col_A_G_B) as (Col_G_A_B & Col_G_B_A & Col_B_A_G & Col_A_B_G & Col_B_G_A).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_H_D) as BetS_D_H_C.
	pose proof (lemma_betweennotequal _ _ _ BetS_C_H_D) as (neq_H_D & neq_C_H & neq_C_D).
	pose proof (lemma_betweennotequal _ _ _ BetS_D_H_C) as (neq_H_C & neq_D_H & neq_D_C).

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_C_H_D) as Col_C_H_D.
	pose proof (lemma_collinearorder _ _ _ Col_C_H_D) as (Col_H_C_D & Col_H_D_C & Col_D_C_H & Col_C_D_H & Col_D_H_C).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_G_H) as BetS_H_G_E.
	pose proof (lemma_betweennotequal _ _ _ BetS_E_G_H) as (neq_G_H & neq_E_G & neq_E_H).
	pose proof (lemma_betweennotequal _ _ _ BetS_H_G_E) as (neq_G_E & neq_H_G & neq_H_E).

	pose proof (lemma_s_onray_assert_ABB _ _ neq_G_H) as OnRay_GH_H.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_H_G) as OnRay_HG_G.

	pose proof (lemma_oppositesidesymmetric _ _ _ _ OS_A_GH_D) as OS_D_GH_A.

	assert (OS_A_GH_D_2 := OS_A_GH_D).
	destruct OS_A_GH_D_2 as (R & BetS_A_R_D & Col_G_H_R & nCol_G_H_A).
	destruct OS_D_GH_A as (_ & _ & _ & nCol_G_H_D).

	pose proof (lemma_NCorder _ _ _ nCol_G_H_A) as (nCol_H_G_A & nCol_H_A_G & nCol_A_G_H & nCol_G_A_H & nCol_A_H_G).
	pose proof (lemma_NCorder _ _ _ nCol_G_H_D) as (_ & _ & _ & _ & nCol_D_H_G).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_G_A_H Col_G_A_B neq_G_B) as nCol_G_B_H.
	pose proof (lemma_NCorder _ _ _ nCol_G_B_H) as (nCol_B_G_H & nCol_B_H_G & nCol_H_G_B & nCol_G_H_B & nCol_H_B_G).
	pose proof (lemma_s_os _ _ _ _ _ BetS_B_G_A Col_G_H_G nCol_G_H_B) as OS_B_GH_A.
	pose proof (lemma_oppositesidesymmetric _ _ _ _ OS_B_GH_A) as OS_A_GH_B.


	pose proof (lemma_equalanglesreflexive _ _ _ nCol_B_G_H) as CongA_BGH_BGH.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_G_H) as CongA_AGH_HGA.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_D_H_G) as CongA_DHG_GHD.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_H_G_A) as CongA_HGA_AGH.
	pose proof (proposition_15a _ _ _ _ _ BetS_A_G_B BetS_H_G_E nCol_A_G_H) as CongA_AGH_EGB.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_AGH_EGB) as CongA_EGB_AGH.

	pose proof (lemma_NChelper _ _ _ _ _ nCol_D_H_G Col_D_H_C Col_D_H_H neq_C_H) as nCol_C_H_G.
	pose proof (lemma_NChelper _ _ _ _ _ nCol_C_H_G Col_C_H_C Col_C_H_D neq_C_D) as nCol_C_D_G.

	pose proof (lemma_NCorder _ _ _ nCol_C_H_G) as (_ & _ & _ & _ & nCol_G_H_C).

	pose proof (proposition_31 _ _ _ _ BetS_C_H_D nCol_C_D_G) as (
		P & Q & S &
		BetS_P_G_Q &
		_ &
		_ &
		_ &
		CongA_PGH_GHD &
		CongA_PGH_DHG &
		CongA_HGP_DHG &
		_ &
		_ &
		_ &
		Cong_GS_SH &
		Cong_PS_SD &
		Cong_CS_SQ &
		BetS_P_S_D &
		BetS_C_S_Q &
		BetS_G_S_H
	).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_G_Q) as BetS_Q_G_P.
	pose proof (lemma_betweennotequal _ _ _ BetS_P_G_Q) as (neq_G_Q & neq_P_G & neq_P_Q).
	pose proof (lemma_betweennotequal _ _ _ BetS_Q_G_P) as (neq_G_P & neq_Q_G & neq_Q_P).

	pose proof (lemma_s_onray_assert_ABB _ _ neq_G_P) as OnRay_GP_P.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_G_Q) as OnRay_GQ_Q.


	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_PGH_GHD) as CongA_GHD_PGH.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_GHD_PGH) as nCol_P_G_H.
	pose proof (lemma_NCorder _ _ _ nCol_P_G_H) as (nCol_G_P_H & nCol_G_H_P & nCol_H_P_G & nCol_P_H_G & nCol_H_G_P).
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_P_G_H) as CongA_PGH_HGP.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_H_G_P) as CongA_HGP_PGH.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_GS_SH) as (_ & _ & Cong_GS_HS).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_PS_SD) as (_ & Cong_SP_SD & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_CS_SQ) as Cong_SQ_CS.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_SQ_CS) as (_ & _ & Cong_SQ_SC).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_S_Q) as BetS_Q_S_C.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_G_S_H) as Col_G_S_H.
	pose proof (lemma_collinearorder _ _ _ Col_G_S_H) as (_ & _ & _ & Col_G_H_S & _).

	pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_G_H_R Col_G_H_S BetS_A_R_D BetS_P_S_D nCol_G_H_A nCol_G_H_P) as SS_A_P_GH.
	pose proof (lemma_samesidesymmetric _ _ _ _ SS_A_P_GH) as (SS_P_A_GH & _ & _).
	pose proof (lemma_planeseparation _ _ _ _ _ SS_P_A_GH OS_A_GH_B) as OS_P_GH_B.

	pose proof (lemma_s_supp _ _ _ _ _ OnRay_GH_H BetS_P_G_Q) as Supp_PGH_HGQ.
	pose proof (lemma_s_supp _ _ _ _ _ OnRay_HG_G BetS_D_H_C) as Supp_DHG_GHC.
	pose proof (lemma_s_supp _ _ _ _ _ OnRay_GH_H BetS_A_G_B) as Supp_AGH_HGB.
	pose proof (lemma_supplement_symmetric _ _ _ _ _ Supp_AGH_HGB) as Supp_BGH_HGA.

	pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_PGH_DHG Supp_PGH_HGQ Supp_DHG_GHC) as CongA_HGQ_GHC.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_HGQ_GHC) as CongA_GHC_HGQ.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_GHC_HGQ) as nCol_H_G_Q.
	pose proof (lemma_NCorder _ _ _ nCol_H_G_Q) as (nCol_G_H_Q & nCol_G_Q_H & nCol_Q_H_G & nCol_H_Q_G & nCol_Q_G_H).

	assert (~ LtA H G A H G P) as n_LtA_HGA_HGP.
	{
		intro LtA_HGA_HGP.

		pose proof (lemma_crossbar_LtA _ _ _ _ _ _ LtA_HGA_HGP SS_A_P_GH OnRay_GH_H OnRay_GP_P) as (M & BetS_P_M_H & OnRay_GA_M).

		pose proof (lemma_onray_strict _ _ _ OnRay_GA_M) as neq_G_M.
		pose proof (lemma_inequalitysymmetric _ _ neq_G_M) as neq_M_G.

		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_GA_M) as Col_G_A_M.
		pose proof (lemma_collinearorder _ _ _ Col_G_A_M) as (_ & _ & Col_M_G_A & _ & _).

		pose proof (postulate_Euclid5 _ _ _ _ _ _ BetS_P_S_D BetS_G_S_H BetS_P_M_H Cong_GS_HS Cong_SP_SD nCol_G_H_D) as (K & BetS_G_M_K & BetS_D_H_K).

		pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_G_M_K) as Col_G_M_K.
		pose proof (lemma_collinearorder _ _ _ Col_G_M_K) as (Col_M_G_K & _ & _ & _ & _).

		pose proof (lemma_s_col_BetS_B_A_C _ _ _ BetS_D_H_K) as Col_H_D_K.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_D_K Col_H_D_C neq_H_D) as Col_D_K_C.
		pose proof (lemma_collinearorder _ _ _ Col_D_K_C) as (_ & _ & Col_C_D_K & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_M_G_A Col_M_G_K neq_M_G) as Col_G_A_K.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_A_B Col_G_A_K neq_G_A) as Col_A_B_K.
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_K Col_C_D_K) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	assert (~ LtA H G P H G A) as n_LtA_HGP_HGA.
	{
		intro LtA_HGP_HGA.

		pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_HGP_HGA CongA_PGH_HGP) as LtA_PGH_HGA.
		pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_PGH_HGA CongA_AGH_HGA) as LtA_PGH_AGH.
		pose proof (lemma_supplementinequality _ _ _ _ _ _ _ _ _ _ Supp_AGH_HGB Supp_PGH_HGQ LtA_PGH_AGH) as LtA_HGB_HGQ.

		destruct OS_P_GH_B as (L & BetS_P_L_B & Col_G_H_L & _).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_L_B) as BetS_B_L_P.

		pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_G_H_L Col_G_H_G BetS_B_L_P BetS_Q_G_P nCol_G_H_B nCol_G_H_Q) as SS_B_Q_GH.

		pose proof (lemma_crossbar_LtA _ _ _ _ _ _ LtA_HGB_HGQ SS_B_Q_GH OnRay_GH_H OnRay_GQ_Q) as (M & BetS_Q_M_H & OnRay_GB_M).

		pose proof (lemma_onray_strict _ _ _ OnRay_GB_M) as neq_G_M.
		pose proof (lemma_inequalitysymmetric _ _ neq_G_M) as neq_M_G.
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_GB_M) as Col_G_B_M.
		pose proof (lemma_collinearorder _ _ _ Col_G_B_M) as (_ & _ & Col_M_G_B & _ & _).

		pose proof (postulate_Euclid5 _ _ _ _ _ _ BetS_Q_S_C BetS_G_S_H BetS_Q_M_H Cong_GS_HS Cong_SQ_SC nCol_G_H_C) as (K & BetS_G_M_K & BetS_C_H_K).

		pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_G_M_K) as Col_G_M_K.
		pose proof (lemma_collinearorder _ _ _ Col_G_M_K) as (Col_M_G_K & _ & _ & _ & _).

		pose proof (lemma_s_col_BetS_B_A_C _ _ _ BetS_C_H_K) as Col_H_C_K.

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_M_G_B Col_M_G_K neq_M_G) as Col_G_B_K.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_B_A Col_G_B_K neq_G_B) as Col_B_A_K.
		pose proof (lemma_collinearorder _ _ _ Col_B_A_K) as (Col_A_B_K & _ & _ & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_C_K Col_H_C_D neq_H_C) as Col_C_K_D.
		pose proof (lemma_collinearorder _ _ _ Col_C_K_D) as (_ & _ & _ & Col_C_D_K & _).
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_K Col_C_D_K) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}


	assert (~ ~ CongA H G A H G P) as n_n_CongA_HGA_HGP.
	{
		intro n_CongA_HGA_HGP.

		pose proof (lemma_angletrichotomy_n_CongA_ABC_DEF_n_LtA_DEF_ABC_LtA_ABC_DEF _ _ _ _ _ _ nCol_H_G_A nCol_H_G_P n_CongA_HGA_HGP n_LtA_HGP_HGA) as LtA_HGA_HGP.

		contradict LtA_HGA_HGP.
		exact n_LtA_HGA_HGP.
	}
	assert (CongA_HGA_HGP := n_n_CongA_HGA_HGP).
	apply Classical_Prop.NNPP in CongA_HGA_HGP.

	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_HGA_HGP CongA_HGP_DHG) as CongA_HGA_DHG.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_AGH_HGA CongA_HGA_DHG) as CongA_AGH_DHG.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_AGH_DHG CongA_DHG_GHD) as CongA_AGH_GHD.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_EGB_AGH CongA_AGH_GHD) as CongA_EGB_GHD.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_AGH_GHD) as CongA_GHD_AGH.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_GHD_AGH CongA_AGH_HGA) as CongA_GHD_HGA.

	pose proof (lemma_s_sumtwort _ _ _ _ _ _ _ _ _ _ _ Supp_BGH_HGA CongA_BGH_BGH CongA_GHD_HGA) as SumTwoRT_BGH_GHD.

	split.
	exact CongA_AGH_GHD.
	split.
	exact CongA_EGB_GHD.
	exact SumTwoRT_BGH_GHD.
Qed.

End Euclid.
