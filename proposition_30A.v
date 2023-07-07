Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
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
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_parallelsymmetric.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_par.
Require Import ProofCheckingEuclid.lemma_s_ss.
Require Import ProofCheckingEuclid.lemma_s_triangle.
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
	OS A G H F ->
	OS F H K C ->
	Par A B C D.
Proof.
	intros A B C D E F G H K.
	intros Par_A_B_E_F.
	intros Par_C_D_E_F.
	intros BetS_G_H_K.
	intros BetS_A_G_B.
	intros BetS_E_H_F.
	intros BetS_C_K_D.
	intros OS_A_G_H_F.
	intros OS_F_H_K_C.

	pose proof (lemma_parallelsymmetric _ _ _ _ Par_C_D_E_F) as Par_E_F_C_D.
	pose proof (lemma_betweennotequal _ _ _ BetS_G_H_K) as (_ & neq_G_H & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_G_H) as neq_H_G.
	pose proof (lemma_extension H G G H neq_H_G neq_G_H) as (P & BetS_H_G_P & Cong_G_P_G_H).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_G_P) as BetS_P_G_H.
	pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_P_G_H BetS_G_H_K) as BetS_P_G_K.

	assert (OS_A_G_H_F_2 := OS_A_G_H_F).
	destruct OS_A_G_H_F_2 as (M & BetS_A_M_F & Col_G_H_M & nCol_G_H_A).
	assert (OS_F_H_K_C_2 := OS_F_H_K_C).
	destruct OS_F_H_K_C_2 as (N & BetS_F_N_C & Col_H_K_N & nCol_H_K_F).

	destruct Par_C_D_E_F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_C_D_E_F & _ & _).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_G_B) as (_ & neq_A_G & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_G) as neq_G_A.
	pose proof (lemma_NCorder _ _ _ nCol_G_H_A) as (_ & _ & nCol_A_G_H & _ & _).
	pose proof (proposition_29 _ _ _ _ _ _ _ Par_A_B_E_F BetS_A_G_B BetS_E_H_F BetS_P_G_H OS_A_G_H_F) as (CongA_A_G_H_G_H_F & _ & _).
	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB G A neq_G_A) as OnRay_G_A_A.
	
	pose proof (lemma_s_onray_assert_bets_ABE G H K BetS_G_H_K neq_G_H) as OnRay_G_H_K.

	pose proof (lemma_equalanglesreflexive _ _ _ nCol_A_G_H) as CongA_A_G_H_A_G_H.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_A_G_H_A_G_H OnRay_G_A_A OnRay_G_H_K) as CongA_A_G_H_A_G_K.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_G_H_A_G_K) as CongA_A_G_K_A_G_H.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_G_K_A_G_H CongA_A_G_H_G_H_F) as CongA_A_G_K_G_H_F.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_N_C) as BetS_C_N_F.
	assert (eq H H) as eq_H_H by (reflexivity).
	pose proof (lemma_NCorder _ _ _ nCol_H_K_F) as (_ & _ & nCol_F_H_K & _ & _).
	pose proof (lemma_s_col_BetS_A_B_C E H F BetS_E_H_F) as Col_E_H_F.
	pose proof (lemma_collinearorder _ _ _ Col_E_H_F) as (_ & _ & _ & _ & Col_F_H_E).
	pose proof (lemma_s_col_eq_B_C F H H eq_H_H) as Col_F_H_H.
	pose proof (lemma_betweennotequal _ _ _ BetS_E_H_F) as (_ & neq_E_H & _).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_F_H_K Col_F_H_E Col_F_H_H neq_E_H) as nCol_E_H_K.
	pose proof (lemma_s_col_eq_B_C E H H eq_H_H) as Col_E_H_H.
	pose proof (lemma_betweennotequal _ _ _ BetS_E_H_F) as (neq_H_F & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_H_F) as neq_F_H.
	pose proof (lemma_s_col_eq_A_C H K H eq_H_H) as Col_H_K_H.
	pose proof (lemma_collinearorder _ _ _ Col_H_K_N) as (Col_K_H_N & _ & _ & _ & _).
	pose proof (lemma_s_col_BetS_A_B_C C K D BetS_C_K_D) as Col_C_K_D.
	pose proof (lemma_betweennotequal _ _ _ BetS_C_K_D) as (_ & neq_C_K & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_C_K_D) as (_ & _ & neq_C_D).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_H_F) as (_ & _ & neq_E_F).
	pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_C_K_D Col_E_H_F neq_C_D neq_E_F neq_C_K neq_H_F n_Meet_C_D_E_F BetS_C_N_F Col_K_H_N) as BetS_K_N_H.
	pose proof (lemma_betweennotequal _ _ _ BetS_K_N_H) as (neq_N_H & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_N_H) as neq_H_N.
	pose proof (lemma_NChelper _ _ _ _ _ nCol_H_K_F Col_H_K_H Col_H_K_N neq_H_N) as nCol_H_N_F.
	pose proof (lemma_NCorder _ _ _ nCol_H_N_F) as (_ & _ & _ & _ & nCol_F_N_H).
	pose proof (lemma_s_col_BetS_A_B_C F N C BetS_F_N_C) as Col_F_N_C.
	assert (eq N N) as eq_N_N by (reflexivity).
	pose proof (lemma_s_col_eq_B_C F N N eq_N_N) as Col_F_N_N.
	pose proof (lemma_betweennotequal _ _ _ BetS_C_N_F) as (_ & neq_C_N & _).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_F_N_H Col_F_N_C Col_F_N_N neq_C_N) as nCol_C_N_H.
	pose proof (lemma_NCorder _ _ _ nCol_C_N_H) as (_ & _ & _ & _ & nCol_H_N_C).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_K_N_H) as BetS_H_N_K.
	pose proof (lemma_s_col_BetS_A_B_C H N K BetS_H_N_K) as Col_H_N_K.
	pose proof (lemma_s_col_eq_A_C H N H eq_H_H) as Col_H_N_H.
	pose proof (lemma_betweennotequal _ _ _ BetS_G_H_K) as (neq_H_K & _ & _).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_H_N_C Col_H_N_H Col_H_N_K neq_H_K) as nCol_H_K_C.
	pose proof (lemma_NCorder _ _ _ nCol_E_H_K) as (_ & nCol_H_K_E & _ & _ & _).
	pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_H_K_H Col_H_K_N BetS_E_H_F BetS_C_N_F nCol_H_K_E nCol_H_K_C) as SS_E_C_H_K.
	assert (eq K K) as eq_K_K by (reflexivity).
	pose proof (lemma_s_col_eq_B_C H K K eq_K_K) as Col_H_K_K.
	pose proof (lemma_s_os _ _ _ _ _ BetS_C_K_D Col_H_K_K nCol_H_K_C) as OS_C_H_K_D.
	pose proof (lemma_planeseparation _ _ _ _ _ SS_E_C_H_K OS_C_H_K_D) as OS_E_H_K_D.
	pose proof (proposition_29 _ _ _ _ _ _ _ Par_E_F_C_D BetS_E_H_F BetS_C_K_D BetS_G_H_K OS_E_H_K_D) as (_ & CongA_G_H_F_H_K_D & _).
	pose proof (lemma_NCorder _ _ _ nCol_H_K_C) as (_ & _ & _ & _ & nCol_C_K_H).
	pose proof (lemma_s_col_eq_B_C C K K eq_K_K) as Col_C_K_K.
	pose proof (lemma_betweennotequal _ _ _ BetS_C_K_D) as (neq_K_D & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_K_D) as neq_D_K.
	pose proof (lemma_NChelper _ _ _ _ _ nCol_C_K_H Col_C_K_D Col_C_K_K neq_D_K) as nCol_D_K_H.
	pose proof (lemma_NCorder _ _ _ nCol_D_K_H) as (_ & _ & _ & _ & nCol_H_K_D).
	pose proof (lemma_equalanglesreflexive _ _ _ nCol_H_K_D) as CongA_H_K_D_H_K_D.
	assert (eq D D) as eq_D_D by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB K D neq_K_D) as OnRay_K_D_D.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_H_K) as BetS_K_H_G.
	pose proof (lemma_betweennotequal _ _ _ BetS_K_H_G) as (_ & neq_K_H & _).
	
	pose proof (lemma_s_onray_assert_bets_ABE K H G BetS_K_H_G neq_K_H) as OnRay_K_H_G.

	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_H_K_D_H_K_D OnRay_K_H_G OnRay_K_D_D) as CongA_H_K_D_G_K_D.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_G_H_F_H_K_D CongA_H_K_D_G_K_D) as CongA_G_H_F_G_K_D.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_G_K_G_H_F CongA_G_H_F_G_K_D) as CongA_A_G_K_G_K_D.
	pose proof (lemma_s_col_BetS_A_B_C G H K BetS_G_H_K) as Col_G_H_K.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_H_M Col_G_H_K neq_G_H) as Col_H_M_K.
	pose proof (lemma_collinearorder _ _ _ Col_H_M_K) as (_ & _ & _ & Col_H_K_M & _).
	pose proof (lemma_collinearorder _ _ _ Col_G_H_K) as (_ & Col_H_K_G & _ & _ & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_K_M Col_H_K_G neq_H_K) as Col_K_M_G.
	pose proof (lemma_collinearorder _ _ _ Col_K_M_G) as (_ & _ & Col_G_K_M & _ & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_K_N Col_H_K_G neq_H_K) as Col_K_N_G.
	pose proof (lemma_collinearorder _ _ _ Col_K_N_G) as (_ & _ & Col_G_K_N & _ & _).
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_A_G_H_A_G_K) as nCol_A_G_K.
	pose proof (lemma_NCorder _ _ _ nCol_A_G_K) as (_ & nCol_G_K_A & _ & _ & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_P_G_K) as (neq_G_K & _ & _).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_H_K_C Col_H_K_G Col_H_K_K neq_G_K) as nCol_G_K_C.
	pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_G_K_M Col_G_K_N BetS_A_M_F BetS_C_N_F nCol_G_K_A nCol_G_K_C) as SS_A_C_G_K.
	pose proof (lemma_s_col_eq_B_C G K K eq_K_K) as Col_G_K_K.
	pose proof (lemma_s_os _ _ _ _ _ BetS_C_K_D Col_G_K_K nCol_G_K_C) as OS_C_G_K_D.
	pose proof (lemma_planeseparation _ _ _ _ _ SS_A_C_G_K OS_C_G_K_D) as OS_A_G_K_D.
	pose proof (proposition_27 _ _ _ _ _ _ BetS_A_G_B BetS_C_K_D CongA_A_G_K_G_K_D OS_A_G_K_D) as Par_A_B_C_D.

	exact Par_A_B_C_D.
Qed.

End Euclid.
