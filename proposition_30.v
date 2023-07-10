Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_30helper.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NChelper.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_collinearparallel.
Require Import ProofCheckingEuclid.lemma_crossimpliesopposite.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_oppositesidesymmetric.
Require Import ProofCheckingEuclid.lemma_parallelNC.
Require Import ProofCheckingEuclid.lemma_parallelflip.
Require Import ProofCheckingEuclid.lemma_parallelsymmetric.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_cross.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_ss.
Require Import ProofCheckingEuclid.proposition_30A.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma parnotmeet :
	forall A B C D,
	Par A B C D ->
	~ Meet A B C D.
Proof.
	intros A B C D.
	intros Par_AB_CD.

	destruct Par_AB_CD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_A_B_C_D & _ & _).
	exact n_Meet_A_B_C_D.
Qed.

Lemma proposition_30 :
	forall A B C D E F G H K,
	Par A B E F ->
	Par C D E F ->
	BetS G H K ->
	Col A B G ->
	Col E F H ->
	Col C D K ->
	neq A G ->
	neq E H ->
	neq C K ->
	Par A B C D.
Proof.
	intros A B C D E F G H K.
	intros Par_AB_EF.
	intros Par_CD_EF.
	intros BetS_G_H_K.
	intros Col_A_B_G.
	intros Col_E_F_H.
	intros Col_C_D_K.
	intros neq_A_G.
	intros neq_E_H.
	intros neq_C_K.

	assert (eq H H) as eq_H_H by (reflexivity).
	assert (eq K K) as eq_K_K by (reflexivity).

	pose proof (lemma_s_col_eq_A_C K H K eq_K_K) as Col_K_H_K.
	pose proof (lemma_s_col_eq_B_C C K K eq_K_K) as Col_C_K_K.
	pose proof (lemma_s_col_eq_B_C E H H eq_H_H) as Col_E_H_H.
	pose proof (lemma_s_col_eq_B_C K H H eq_H_H) as Col_K_H_H.

	pose proof (lemma_parallelsymmetric _ _ _ _ Par_AB_EF) as Par_EF_AB.
	pose proof (lemma_parallelflip _ _ _ _ Par_EF_AB) as (_ & Par_EF_BA & _).
	pose proof (lemma_parallelflip _ _ _ _ Par_AB_EF) as (_ & Par_AB_FE & _).
	pose proof (lemma_parallelNC _ _ _ _ Par_AB_EF) as (nCol_A_B_E & _ & _ & _).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_E) as (_ & _ & _ & neq_B_A & _ & _).

	pose proof (lemma_parallelflip _ _ _ _ Par_CD_EF) as (_ & Par_CD_FE & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_CD_EF) as Par_EF_CD.
	pose proof (lemma_parallelflip _ _ _ _ Par_EF_CD) as (_ & Par_EF_DC & _).
	pose proof (lemma_parallelNC _ _ _ _ Par_CD_EF) as (nCol_C_D_E & _ & _ & _).
	pose proof (lemma_NCdistinct _ _ _ nCol_C_D_E) as (neq_C_D & _ & _ & _ & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_C_D) as neq_D_C.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_H_K) as BetS_K_H_G.

	pose proof (lemma_collinearorder _ _ _ Col_A_B_G) as (_ & _ & Col_G_A_B & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_G) as (Col_B_A_G & _ & _ & _ & _).

	pose proof (lemma_collinearorder _ _ _ Col_E_F_H) as (Col_F_E_H & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_E_F_H) as (_ & _ & Col_H_E_F & _ & _).

	pose proof (lemma_collinearorder _ _ _ Col_C_D_K) as (Col_D_C_K & _ & _ & _ & _).

	pose proof (lemma_inequalitysymmetric _ _ neq_A_G) as neq_G_A.
	pose proof (lemma_inequalitysymmetric _ _ neq_E_H) as neq_H_E.
	pose proof (lemma_inequalitysymmetric _ _ neq_C_K) as neq_K_C.

	pose proof (lemma_collinearparallel _ _ _ _ _ Par_AB_FE Col_F_E_H neq_H_E) as Par_AB_HE.
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_CD_FE Col_F_E_H neq_H_E) as Par_CD_HE.

	pose proof (lemma_parallelflip _ _ _ _ Par_AB_HE) as (_ & Par_AB_EH & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_AB_EH) as Par_EH_AB.
	pose proof (lemma_parallelflip _ _ _ _ Par_EH_AB) as (_ & Par_EH_BA & _).
	pose proof (lemma_parallelflip _ _ _ _ Par_CD_HE) as (_ & Par_CD_EH & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_CD_EH) as Par_EH_CD.
	pose proof (lemma_parallelflip _ _ _ _ Par_EH_CD) as (_ & Par_EH_DC & _).

	pose proof (postulate_Euclid2 _ _ neq_A_G) as (b & BetS_A_G_b).
	pose proof (postulate_Euclid2 _ _ neq_E_H) as (f & BetS_E_H_f).
	pose proof (postulate_Euclid2 _ _ neq_C_K) as (d & BetS_C_K_d).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_G_b) as (_ & _ & neq_A_b).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_b) as neq_b_A.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_G_b) as Col_A_G_b.
	pose proof (lemma_collinearorder _ _ _ Col_A_G_b) as (Col_G_A_b & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_G_A_b) as (_ & Col_A_b_G & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_b_G) as (Col_b_A_G & _ & _ & _ & _).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_A_b Col_G_A_B neq_G_A) as Col_A_b_B.
	pose proof (lemma_collinearorder _ _ _ Col_A_b_B) as (_ & _ & Col_B_A_b & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_b_B) as (Col_b_A_B & _ & _ & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_H_f) as BetS_f_H_E.
	pose proof (lemma_betweennotequal _ _ _ BetS_E_H_f) as (_ & _ & neq_E_f).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_H_f) as (neq_H_f & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_H_f) as neq_f_H.
	pose proof (lemma_inequalitysymmetric _ _ neq_E_f) as neq_f_E.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_E_H_f) as Col_E_H_f.
	pose proof (lemma_collinearorder _ _ _ Col_E_H_f) as (Col_H_E_f & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_H_E_f) as (_ & Col_E_f_H & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_E_f_H) as (Col_f_E_H & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_E_f_H) as (_ & Col_f_H_E & _ & _ & _).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_E_f Col_H_E_F neq_H_E) as Col_E_f_F.
	pose proof (lemma_collinearorder _ _ _ Col_E_f_F) as (_ & _ & Col_F_E_f & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_K_d) as BetS_d_K_C.
	pose proof (lemma_betweennotequal _ _ _ BetS_C_K_d) as (_ & _ & neq_C_d).
	pose proof (lemma_betweennotequal _ _ _ BetS_C_K_d) as (neq_K_d & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_C_d) as neq_d_C.
	pose proof (lemma_inequalitysymmetric _ _ neq_K_d) as neq_d_K.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_C_K_d) as Col_C_K_d.
	pose proof (lemma_collinearorder _ _ _ Col_C_K_d) as (Col_K_C_d & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_K_d) as (_ & _ & Col_d_C_K & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_D_K) as (_ & _ & Col_K_C_D & _ & _).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_K_C_d Col_K_C_D neq_K_C) as Col_C_d_D.
	pose proof (lemma_collinearorder _ _ _ Col_C_d_D) as (Col_d_C_D & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_d_D) as (_ & _ & Col_D_C_d & _ & _).

	pose proof (lemma_collinearparallel _ _ _ _ _ Par_EF_DC Col_D_C_d neq_d_C) as Par_EF_dC.
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_EF_BA Col_B_A_b neq_b_A) as Par_EF_bA.
	pose proof (lemma_parallelflip _ _ _ _ Par_EF_bA) as (_ & Par_EF_Ab & _).
	pose proof (lemma_parallelflip _ _ _ _ Par_EF_dC) as (_ & Par_EF_Cd & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_EF_Ab) as Par_Ab_EF.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_EF_Cd) as Par_Cd_EF.
	pose proof (lemma_parallelflip _ _ _ _ Par_Ab_EF) as (_ & Par_Ab_FE & _).
	pose proof (lemma_parallelflip _ _ _ _ Par_Cd_EF) as (_ & Par_Cd_FE & _).

	pose proof (lemma_collinearparallel _ _ _ _ _ Par_Ab_FE Col_F_E_f neq_f_E) as Par_Ab_fE.
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_Cd_FE Col_F_E_f neq_f_E) as Par_Cd_fE.
	pose proof (lemma_parallelflip _ _ _ _ Par_Ab_fE) as (_ & Par_Ab_Ef & _).
	pose proof (lemma_parallelflip _ _ _ _ Par_Cd_fE) as (_ & Par_Cd_Ef & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_Cd_fE) as Par_fE_Cd.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_Cd_Ef) as Par_Ef_Cd.
	pose proof (lemma_parallelflip _ _ _ _ Par_Cd_Ef) as (Par_dC_Ef & _ & _).
	pose proof (lemma_parallelflip _ _ _ _ Par_Cd_fE) as (Par_dC_fE & _ & _).

	pose proof (parnotmeet _ _ _ _ Par_Ef_Cd) as n_Meet_E_f_C_d.
	pose proof (parnotmeet _ _ _ _ Par_fE_Cd) as n_Meet_f_E_C_d.

	pose proof (lemma_collinearparallel _ _ _ _ _ Par_Ab_fE Col_f_E_H neq_H_E) as Par_Ab_HE.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_Ab_HE) as Par_HE_Ab.
	pose proof (lemma_parallelflip _ _ _ _ Par_HE_Ab) as (_ & _ & Par_EH_bA).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_EH_bA Col_b_A_G neq_G_A) as Par_EH_GA.

	pose proof (lemma_parallelflip _ _ _ _ Par_EH_GA) as (_ & Par_EH_AG & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_EH_AG) as Par_AG_EH.
	pose proof (lemma_parallelNC _ _ _ _ Par_AG_EH) as (_ & _ & _ & nCol_A_G_H).

	pose proof (lemma_collinearparallel _ _ _ _ _ Par_Cd_fE Col_f_E_H neq_H_E) as Par_Cd_HE.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_Cd_HE) as Par_HE_Cd.
	pose proof (lemma_parallelflip _ _ _ _ Par_HE_Cd) as (_ & Par_HE_dC & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_HE_dC Col_d_C_K neq_K_C) as Par_HE_KC.
	pose proof (lemma_parallelflip _ _ _ _ Par_HE_KC) as (_ & _ & Par_EH_CK).

	pose proof (lemma_parallelNC _ _ _ _ Par_EH_CK) as (_ & _ & _ & nCol_E_H_K).
	pose proof (lemma_NCorder _ _ _ nCol_E_H_K) as (_ & _ & _ & _ & nCol_K_H_E).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_EH_DC Col_D_C_K neq_K_C) as Par_EH_KC.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_EH_CK) as Par_CK_EH.
	pose proof (lemma_parallelNC _ _ _ _ Par_CK_EH) as (_ & _ & _ & nCol_C_K_H).
	pose proof (lemma_NCorder _ _ _ nCol_C_K_H) as (_ & nCol_K_H_C & _ & _ & _).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_E_H_K Col_E_H_f Col_E_H_H neq_f_H) as nCol_f_H_K.
	pose proof (lemma_NCorder _ _ _ nCol_f_H_K) as (_ & _ & _ & _ & nCol_K_H_f).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_C_K_H Col_C_K_d Col_C_K_K neq_d_K) as nCol_d_K_H.

	pose proof (lemma_s_os _ _ _ _ _ BetS_C_K_d Col_K_H_K nCol_K_H_C) as OppositeSide_C_KH_d.


	assert (~ ~ (Cross A f G H \/ Cross A E G H)) as n_n_Cross_Af_GH_or_Cross_AE_GH.
	{
		intro n_Cross_Af_GH_and_n_Cross_AE_GH.

		apply Classical_Prop.not_or_and in n_Cross_Af_GH_and_n_Cross_AE_GH.
		destruct n_Cross_Af_GH_and_n_Cross_AE_GH as (n_Cross_Af_GH & n_Cross_AE_GH).

		pose proof (lemma_30helper _ _ _ _ _ _ Par_Ab_Ef BetS_A_G_b BetS_E_H_f n_Cross_Af_GH) as Cross_AE_GH.

		contradict Cross_AE_GH.
		exact n_Cross_AE_GH.
	}
	assert (Cross_Af_GH_or_Cross_AE_GH := n_n_Cross_Af_GH_or_Cross_AE_GH).
	apply Classical_Prop.NNPP in Cross_Af_GH_or_Cross_AE_GH.


	assert (~ ~ (Cross C f K H \/ Cross C E K H)) as n_n_Cross_Cf_KH_or_Cross_CE_KH.
	{
		intro n_Cross_Cf_KH_and_n_Cross_CE_KH.

		apply Classical_Prop.not_or_and in n_Cross_Cf_KH_and_n_Cross_CE_KH.
		destruct n_Cross_Cf_KH_and_n_Cross_CE_KH as (n_Cross_Cf_KH & n_Cross_CE_KH).

		pose proof (lemma_30helper _ _ _ _ _ _ Par_Cd_Ef BetS_C_K_d BetS_E_H_f n_Cross_Cf_KH) as Cross_CE_KH.

		contradict Cross_CE_KH.
		exact n_Cross_CE_KH.
	}
	assert (Cross_Cf_KH_or_Cross_CE_KH := n_n_Cross_Cf_KH_or_Cross_CE_KH).
	apply Classical_Prop.NNPP in Cross_Cf_KH_or_Cross_CE_KH.


	(* assert by cases *)
	assert (Par A b C d) as Par_Ab_Cd.
	destruct Cross_Af_GH_or_Cross_AE_GH as [Cross_Af_GH | Cross_AE_GH].
	{
		(* case Cross_Af_GH *)
		pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_Af_GH nCol_A_G_H) as (OppositeSide_A_GH_f & _ & _ & _).

		(* assert by cases *)
		assert (Par A b C d) as Par_Ab_Cd.
		destruct Cross_Cf_KH_or_Cross_CE_KH as [Cross_Cf_KH | Cross_CE_KH].
		{
			(* case Cross_Cf_KH *)
			pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_Cf_KH nCol_C_K_H) as (_ & _ & _ & OppositeSide_f_HK_C).
			pose proof (proposition_30A _ _ _ _ _ _ _ _ _ Par_Ab_Ef Par_Cd_Ef BetS_G_H_K BetS_A_G_b BetS_E_H_f BetS_C_K_d OppositeSide_A_GH_f OppositeSide_f_HK_C) as Par_Ab_Cd.

			exact Par_Ab_Cd.
		}
		{
			(* case Cross_CE_KH *)

			destruct Cross_CE_KH as (M & BetS_C_M_E & BetS_K_M_H).

			pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_K_M_H) as Col_K_M_H.
			pose proof (lemma_collinearorder _ _ _ Col_K_M_H) as (_ & _ & _ & Col_K_H_M & _).

			pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_K_H_H Col_K_H_M BetS_f_H_E BetS_C_M_E nCol_K_H_f nCol_K_H_C) as SameSide_f_C_KH.
			pose proof (lemma_planeseparation _ _ _ _ _ SameSide_f_C_KH OppositeSide_C_KH_d) as OppositeSide_f_KH_d.

			destruct OppositeSide_f_KH_d as (m & BetS_f_m_d & Col_K_H_m & _).

			pose proof (axiom_betweennesssymmetry _ _ _ BetS_f_m_d) as BetS_d_m_f.

			pose proof (lemma_collinearorder _ _ _ Col_K_H_m) as (Col_H_K_m & _ & _ & _ & _).

			pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_f_H_E Col_C_K_d neq_f_E neq_C_d neq_f_H neq_K_d n_Meet_f_E_C_d BetS_f_m_d Col_H_K_m) as BetS_H_m_K.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_m_K) as BetS_K_m_H.

			pose proof (lemma_s_cross _ _ _ _ _ BetS_d_m_f BetS_K_m_H) as Cross_df_KH.
			pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_df_KH nCol_d_K_H) as (_ & OppositeSide_d_HK_f & _ & _).
			pose proof (lemma_oppositesidesymmetric _ _ _ _ OppositeSide_d_HK_f) as OppositeSide_f_HK_d.

			pose proof (proposition_30A _ _ _ _ _ _ _ _ _ Par_Ab_Ef Par_dC_Ef BetS_G_H_K BetS_A_G_b BetS_E_H_f BetS_d_K_C OppositeSide_A_GH_f OppositeSide_f_HK_d) as Par_Ab_dC.
			pose proof (lemma_parallelflip _ _ _ _ Par_Ab_dC) as (_ & Par_Ab_Cd & _).

			exact Par_Ab_Cd.
		}

		exact Par_Ab_Cd.
	}
	{
		(* case Cross_AE_GH *)

		(* assert by cases *)
		assert (Par A b C d) as Par_Ab_Cd.
		destruct Cross_Cf_KH_or_Cross_CE_KH as [Cross_Cf_KH | Cross_CE_KH].
		{
			(* case Cross_Cf_KH *)

			destruct Cross_Cf_KH as (M & BetS_C_M_f & BetS_K_M_H).

			pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_K_M_H) as Col_K_M_H.
			pose proof (lemma_collinearorder _ _ _ Col_K_M_H) as (_ & _ & _ & Col_K_H_M & _).

			pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_K_H_H Col_K_H_M BetS_E_H_f BetS_C_M_f nCol_K_H_E nCol_K_H_C) as SameSide_E_C_KH.
			pose proof (lemma_planeseparation _ _ _ _ _ SameSide_E_C_KH OppositeSide_C_KH_d) as OppositeSide_E_KH_d.

			destruct OppositeSide_E_KH_d as (m & BetS_E_m_d & Col_K_H_m & _).

			pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_m_d) as BetS_d_m_E.

			pose proof (lemma_collinearorder _ _ _ Col_K_H_m) as (Col_H_K_m & _ & _ & _ & _).

			pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_E_H_f Col_C_K_d neq_E_f neq_C_d neq_E_H neq_K_d n_Meet_E_f_C_d BetS_E_m_d Col_H_K_m) as BetS_H_m_K.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_m_K) as BetS_K_m_H.

			pose proof (lemma_s_cross _ _ _ _ _ BetS_d_m_E BetS_K_m_H) as Cross_dE_KH.

			pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_dE_KH nCol_d_K_H) as (_ & OppositeSide_d_HK_E & _ & _).
			pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_AE_GH nCol_A_G_H) as (OppositeSide_A_GH_E & _ & _ & _).
			pose proof (lemma_oppositesidesymmetric _ _ _ _ OppositeSide_d_HK_E) as OppositeSide_E_HK_d.

			pose proof (proposition_30A _ _ _ _ _ _ _ _ _ Par_Ab_fE Par_dC_fE BetS_G_H_K BetS_A_G_b BetS_f_H_E BetS_d_K_C OppositeSide_A_GH_E OppositeSide_E_HK_d) as Par_Ab_dC.
			pose proof (lemma_parallelflip _ _ _ _ Par_Ab_dC) as (_ & Par_Ab_Cd & _).

			exact Par_Ab_Cd.
		}
		{
			(* case Cross_CE_KH *)
			pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_CE_KH nCol_C_K_H) as (_ & OppositeSide_C_HK_E & _ & _).
			pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_AE_GH nCol_A_G_H) as (OppositeSide_A_GH_E & _ & _ & _).
			pose proof (lemma_oppositesidesymmetric _ _ _ _ OppositeSide_C_HK_E) as OppositeSide_E_HK_C.

			pose proof (proposition_30A _ _ _ _ _ _ _ _ _ Par_Ab_fE Par_Cd_fE BetS_G_H_K BetS_A_G_b BetS_f_H_E BetS_C_K_d OppositeSide_A_GH_E OppositeSide_E_HK_C) as Par_Ab_Cd.

			exact Par_Ab_Cd.
		}

		exact Par_Ab_Cd.
	}
	pose proof (lemma_parallelflip _ _ _ _ Par_Ab_Cd) as (_ & Par_Ab_dC & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_Ab_dC Col_d_C_D neq_D_C) as Par_Ab_DC.
	pose proof (lemma_parallelflip _ _ _ _ Par_Ab_DC) as (_ & Par_Ab_CD & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_Ab_CD) as Par_CD_Ab.
	pose proof (lemma_parallelflip _ _ _ _ Par_CD_Ab) as (_ & Par_CD_bA & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_CD_bA Col_b_A_B neq_B_A) as Par_CD_BA.
	pose proof (lemma_parallelflip _ _ _ _ Par_CD_BA) as (_ & Par_CD_AB & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_CD_AB) as Par_AB_CD.

	exact Par_AB_CD.
Qed.

End Euclid.
