Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NChelper.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_parallelsymmetric.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_ss.
Require Import ProofCheckingEuclid.proposition_27.
Require Import ProofCheckingEuclid.proposition_29.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_30A :
	forall A B C D E F G H K,
	Par A B E F ->
	Par C D E F ->
	BetS G H K ->
	BetS A G B ->
	BetS E H F ->
	BetS C K D ->
	OppositeSide A G H F ->
	OppositeSide F H K C ->
	Par A B C D.
Proof.
	intros A B C D E F G H K.
	intros Par_AB_EF.
	intros Par_CD_EF.
	intros BetS_G_H_K.
	intros BetS_A_G_B.
	intros BetS_E_H_F.
	intros BetS_C_K_D.
	intros OppositeSide_A_GH_F.
	intros OppositeSide_F_HK_C.

	assert (eq H H) as eq_H_H by (reflexivity).
	assert (eq K K) as eq_K_K by (reflexivity).

	pose proof (lemma_s_col_eq_A_C H K H eq_H_H) as Col_H_K_H.
	pose proof (lemma_s_col_eq_B_C C K K eq_K_K) as Col_C_K_K.
	pose proof (lemma_s_col_eq_B_C E H H eq_H_H) as Col_E_H_H.
	pose proof (lemma_s_col_eq_B_C F H H eq_H_H) as Col_F_H_H.
	pose proof (lemma_s_col_eq_B_C G K K eq_K_K) as Col_G_K_K.
	pose proof (lemma_s_col_eq_B_C H K K eq_K_K) as Col_H_K_K.

	pose proof (lemma_parallelsymmetric _ _ _ _ Par_CD_EF) as Par_EF_CD.

	destruct Par_CD_EF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_C_D_E_F & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_H_K) as BetS_K_H_G.
	pose proof (lemma_betweennotequal _ _ _ BetS_G_H_K) as (_ & neq_G_H & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_G_H_K) as (neq_H_K & _ & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_G_H_K) as (_ & _ & neq_G_K).
	pose proof (lemma_betweennotequal _ _ _ BetS_K_H_G) as (_ & neq_K_H & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_G_H) as neq_H_G.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_G_H_K) as Col_G_H_K.
	pose proof (lemma_collinearorder _ _ _ Col_G_H_K) as (_ & Col_H_K_G & _ & _ & _).

	pose proof (lemma_s_onray_assert_bets_ABE _ _ _ BetS_G_H_K neq_G_H) as OnRay_GH_K.
	pose proof (lemma_s_onray_assert_bets_ABE _ _ _ BetS_K_H_G neq_K_H) as OnRay_KH_G.

	pose proof (lemma_betweennotequal _ _ _ BetS_A_G_B) as (_ & neq_A_G & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_G) as neq_G_A.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_G_A) as OnRay_GA_A.

	pose proof (lemma_betweennotequal _ _ _ BetS_E_H_F) as (_ & _ & neq_E_F).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_H_F) as (_ & neq_E_H & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_H_F) as (neq_H_F & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_H_F) as neq_F_H.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_E_H_F) as Col_E_H_F.
	pose proof (lemma_collinearorder _ _ _ Col_E_H_F) as (_ & _ & _ & _ & Col_F_H_E).

	pose proof (lemma_betweennotequal _ _ _ BetS_C_K_D) as (_ & _ & neq_C_D).
	pose proof (lemma_betweennotequal _ _ _ BetS_C_K_D) as (_ & neq_C_K & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_C_K_D) as (neq_K_D & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_K_D) as neq_D_K.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_C_K_D) as Col_C_K_D.

	pose proof (lemma_s_onray_assert_ABB _ _ neq_K_D) as OnRay_KD_D.

	assert (OppositeSide_A_GH_F_2 := OppositeSide_A_GH_F).
	destruct OppositeSide_A_GH_F_2 as (M & BetS_A_M_F & Col_G_H_M & nCol_G_H_A).
	assert (OppositeSide_F_HK_C_2 := OppositeSide_F_HK_C).
	destruct OppositeSide_F_HK_C_2 as (N & BetS_F_N_C & Col_H_K_N & nCol_H_K_F).

	assert (eq N N) as eq_N_N by (reflexivity).

	pose proof (lemma_s_col_eq_A_C H N H eq_H_H) as Col_H_N_H.
	pose proof (lemma_s_col_eq_B_C F N N eq_N_N) as Col_F_N_N.

	pose proof (lemma_NCorder _ _ _ nCol_G_H_A) as (_ & _ & nCol_A_G_H & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_N_C) as BetS_C_N_F.
	pose proof (lemma_betweennotequal _ _ _ BetS_C_N_F) as (_ & neq_C_N & _).

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_F_N_C) as Col_F_N_C.

	pose proof (lemma_collinearorder _ _ _ Col_H_K_N) as (Col_K_H_N & _ & _ & _ & _).

	pose proof (lemma_NCorder _ _ _ nCol_H_K_F) as (_ & _ & nCol_F_H_K & _ & _).

	pose proof (lemma_NChelper _ _ _ _ _ nCol_F_H_K Col_F_H_E Col_F_H_H neq_E_H) as nCol_E_H_K.
	pose proof (lemma_NCorder _ _ _ nCol_E_H_K) as (_ & nCol_H_K_E & _ & _ & _).

	pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_C_K_D Col_E_H_F neq_C_D neq_E_F neq_C_K neq_H_F n_Meet_C_D_E_F BetS_C_N_F Col_K_H_N) as BetS_K_N_H.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_K_N_H) as BetS_H_N_K.
	pose proof (lemma_betweennotequal _ _ _ BetS_K_N_H) as (neq_N_H & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_N_H) as neq_H_N.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_H_N_K) as Col_H_N_K.

	pose proof (lemma_NChelper _ _ _ _ _ nCol_H_K_F Col_H_K_H Col_H_K_N neq_H_N) as nCol_H_N_F.
	pose proof (lemma_NCorder _ _ _ nCol_H_N_F) as (_ & _ & _ & _ & nCol_F_N_H).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_F_N_H Col_F_N_C Col_F_N_N neq_C_N) as nCol_C_N_H.
	pose proof (lemma_NCorder _ _ _ nCol_C_N_H) as (_ & _ & _ & _ & nCol_H_N_C).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_H_N_C Col_H_N_H Col_H_N_K neq_H_K) as nCol_H_K_C.
	pose proof (lemma_NCorder _ _ _ nCol_H_K_C) as (_ & _ & _ & _ & nCol_C_K_H).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_C_K_H Col_C_K_D Col_C_K_K neq_D_K) as nCol_D_K_H.
	pose proof (lemma_NCorder _ _ _ nCol_D_K_H) as (_ & _ & _ & _ & nCol_H_K_D).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_H_K_C Col_H_K_G Col_H_K_K neq_G_K) as nCol_G_K_C.

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_H_M Col_G_H_K neq_G_H) as Col_H_M_K.
	pose proof (lemma_collinearorder _ _ _ Col_H_M_K) as (_ & _ & _ & Col_H_K_M & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_K_M Col_H_K_G neq_H_K) as Col_K_M_G.
	pose proof (lemma_collinearorder _ _ _ Col_K_M_G) as (_ & _ & Col_G_K_M & _ & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_K_N Col_H_K_G neq_H_K) as Col_K_N_G.
	pose proof (lemma_collinearorder _ _ _ Col_K_N_G) as (_ & _ & Col_G_K_N & _ & _).

	pose proof (lemma_equalanglesreflexive _ _ _ nCol_H_K_D) as CongA_HKD_HKD.
	pose proof (lemma_equalanglesreflexive _ _ _ nCol_A_G_H) as CongA_AGH_AGH.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_AGH_AGH OnRay_GA_A OnRay_GH_K) as CongA_AGH_AGK.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_AGH_AGK) as CongA_AGK_AGH.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_AGH_AGK) as nCol_A_G_K.
	pose proof (lemma_NCorder _ _ _ nCol_A_G_K) as (_ & nCol_G_K_A & _ & _ & _).

	pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_H_K_H Col_H_K_N BetS_E_H_F BetS_C_N_F nCol_H_K_E nCol_H_K_C) as SameSide_E_C_HK.
	pose proof (lemma_s_os _ _ _ _ _ BetS_C_K_D Col_H_K_K nCol_H_K_C) as OppositeSide_C_HK_D.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_E_C_HK OppositeSide_C_HK_D) as OppositeSide_E_HK_D.
	pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_G_K_M Col_G_K_N BetS_A_M_F BetS_C_N_F nCol_G_K_A nCol_G_K_C) as SameSide_A_C_GK.
	pose proof (lemma_s_os _ _ _ _ _ BetS_C_K_D Col_G_K_K nCol_G_K_C) as OppositeSide_C_GK_D.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_A_C_GK OppositeSide_C_GK_D) as OppositeSide_A_GK_D.

	pose proof (postulate_Euclid2 _ _ neq_H_G) as (P & BetS_H_G_P).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_G_P) as BetS_P_G_H.

	pose proof (proposition_29 _ _ _ _ _ _ _ Par_AB_EF BetS_A_G_B BetS_E_H_F BetS_P_G_H OppositeSide_A_GH_F) as (CongA_AGH_GHF & _ & _).
	pose proof (proposition_29 _ _ _ _ _ _ _ Par_EF_CD BetS_E_H_F BetS_C_K_D BetS_G_H_K OppositeSide_E_HK_D) as (_ & CongA_GHF_HKD & _).

	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_AGK_AGH CongA_AGH_GHF) as CongA_AGK_GHF.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_HKD_HKD OnRay_KH_G OnRay_KD_D) as CongA_HKD_GKD.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_GHF_HKD CongA_HKD_GKD) as CongA_GHF_GKD.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_AGK_GHF CongA_GHF_GKD) as CongA_AGK_GKD.

	pose proof (proposition_27 _ _ _ _ _ _ BetS_A_G_B BetS_C_K_D CongA_AGK_GKD OppositeSide_A_GK_D) as Par_AB_CD.

	exact Par_AB_CD.
Qed.

End Euclid.
