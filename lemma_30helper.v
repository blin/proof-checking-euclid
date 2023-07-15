Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_collinearparallel.
Require Import ProofCheckingEuclid.lemma_crisscross.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_parallelNC.
Require Import ProofCheckingEuclid.lemma_parallelflip.
Require Import ProofCheckingEuclid.lemma_parallelsymmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Cross.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_30helper :
	forall A B E F G H,
	Par A B E F ->
	BetS A G B ->
	BetS E H F ->
	~ Cross A F G H ->
	Cross A E G H.
Proof.
	intros A B E F G H.
	intros Par_AB_EF.
	intros BetS_A_G_B.
	intros BetS_E_H_F.
	intros n_Cross_AF_GH.

	pose proof (lemma_parallelflip _ _ _ _ Par_AB_EF) as (_ & Par_AB_FE & _).
	pose proof (lemma_parallelNC _ _ _ _ Par_AB_EF) as (_ & nCol_A_E_F & _ & _).

	pose proof (lemma_NCorder _ _ _ nCol_A_E_F) as (_ & _ & _ & _ & nCol_F_E_A).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_G_B) as (_ & neq_A_G & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_G_B) as (_ & _ & neq_A_B).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_G_B) as (neq_G_B & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_G) as neq_G_A.
	pose proof (lemma_inequalitysymmetric _ _ neq_G_B) as neq_B_G.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_G_B) as Col_A_G_B.
	pose proof (lemma_collinearorder _ _ _ Col_A_G_B) as (_ & _ & Col_B_A_G & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_G_B) as (Col_G_A_B & _ & _ & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_H_F) as BetS_F_H_E.
	pose proof (lemma_betweennotequal _ _ _ BetS_E_H_F) as (neq_H_F & _ & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_H_F) as (_ & neq_E_H & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_H_F) as (_ & _ & neq_E_F).
	pose proof (lemma_inequalitysymmetric _ _ neq_E_F) as neq_F_E.
	pose proof (lemma_inequalitysymmetric _ _ neq_E_H) as neq_H_E.
	pose proof (lemma_inequalitysymmetric _ _ neq_H_F) as neq_F_H.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_E_H_F) as Col_E_H_F.
	pose proof (lemma_collinearorder _ _ _ Col_E_H_F) as (_ & _ & _ & Col_E_F_H & _).
	pose proof (lemma_collinearorder _ _ _ Col_E_F_H) as (Col_F_E_H & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_E_H_F) as (_ & Col_H_F_E & _ & _ & _).

	pose proof (lemma_collinearparallel _ _ _ _ _ Par_AB_FE Col_F_E_H neq_H_E) as Par_AB_HE.
	destruct Par_AB_HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_A_B_H_E & _ & _).

	pose proof (lemma_collinearparallel _ _ _ _ _ Par_AB_EF Col_E_F_H neq_H_F) as Par_AB_HF.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_AB_HF) as Par_HF_AB.
	pose proof (lemma_parallelflip _ _ _ _ Par_HF_AB) as (_ & Par_HF_BA & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_HF_BA Col_B_A_G neq_G_A) as Par_HF_GA.
	pose proof (lemma_parallelflip _ _ _ _ Par_HF_GA) as (_ & Par_HF_AG & _).

	pose proof (lemma_collinearparallel _ _ _ _ _ Par_HF_AG Col_A_G_B neq_B_G) as Par_HF_BG.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_HF_BG) as Par_BG_HF.
	pose proof (lemma_parallelflip _ _ _ _ Par_BG_HF) as (_ & _ & Par_GB_FH).
	destruct Par_GB_FH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_G_B_F_H & _ & _).

	pose proof (lemma_parallelsymmetric _ _ _ _ Par_HF_AG) as Par_AG_HF.
	pose proof (lemma_parallelflip _ _ _ _ Par_AG_HF) as (_ & Par_AG_FH & _).

	pose proof (lemma_parallelNC _ _ _ _ Par_AG_HF) as (nCol_A_G_H & _ & _ & _).
	pose proof (lemma_NCorder _ _ _ nCol_A_G_H) as (_ & _ & _ & nCol_A_H_G & _).

	pose proof (lemma_crisscross _ _ _ _ Par_AG_FH n_Cross_AF_GH) as Cross_AH_FG.

	destruct Cross_AH_FG as (M & BetS_A_M_H & BetS_F_M_G).

	pose proof (lemma_betweennotequal _ _ _ BetS_F_M_G) as (_ & neq_F_M & _).
	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_F_M_G) as Col_F_M_G.

	pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_A_M_H BetS_F_H_E nCol_F_E_A) as (p & BetS_A_p_E & BetS_F_M_p).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_p_E) as (_ & neq_A_p & _).
	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_p_E) as Col_A_p_E.

	pose proof (lemma_betweennotequal _ _ _ BetS_F_M_p) as (neq_M_p & _ & _).
	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_F_M_p) as Col_F_M_p.
	pose proof (lemma_collinearorder _ _ _ Col_F_M_p) as (_ & Col_M_p_F & _ & _ & _).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_F_M_G Col_F_M_p neq_F_M) as Col_M_G_p.
	pose proof (lemma_collinearorder _ _ _ Col_M_G_p) as (_ & _ & _ & Col_M_p_G & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_M_p_G Col_M_p_F neq_M_p) as Col_p_G_F.
	pose proof (lemma_collinearorder _ _ _ Col_p_G_F) as (_ & Col_G_F_p & _ & _ & _).

	pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_A_G_B Col_H_F_E neq_A_B neq_H_E neq_A_G neq_F_E n_Meet_A_B_H_E BetS_A_p_E Col_G_F_p) as BetS_G_p_F.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_p_F) as BetS_F_p_G.
	pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_F_M_p BetS_F_p_G) as BetS_M_p_G.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_M_p_G) as BetS_G_p_M.

	pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_G_p_M BetS_A_M_H nCol_A_H_G) as (m & BetS_G_m_H & BetS_A_p_m).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_p_m) as (neq_p_m & _ & _).
	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_p_m) as Col_A_p_m.
	pose proof (lemma_collinearorder _ _ _ Col_A_p_m) as (_ & Col_p_m_A & _ & _ & _).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_p_m Col_A_p_E neq_A_p) as Col_p_m_E.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_p_m_E Col_p_m_A neq_p_m) as Col_m_E_A.
	pose proof (lemma_collinearorder _ _ _ Col_m_E_A) as (_ & _ & _ & _ & Col_A_E_m).

	pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_G_A_B Col_F_E_H neq_G_B neq_F_H neq_G_A neq_E_H n_Meet_G_B_F_H BetS_G_m_H Col_A_E_m) as BetS_A_m_E.

	pose proof (by_def_Cross _ _ _ _ _ BetS_A_m_E BetS_G_m_H) as Cross_AE_GH.

	exact Cross_AE_GH.
Qed.

End Euclid.
