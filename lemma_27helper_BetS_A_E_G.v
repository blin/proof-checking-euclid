Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_OnRay.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_SameSide.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.proposition_16.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_27helper_BetS_A_E_G :
	forall A B C D E F G,
	BetS A E B ->
	BetS C F D ->
	OppositeSide A E F D ->
	Col A B G ->
	Col C D G ->
	nCol E F D ->
	BetS A E G ->
	LtA F E B E F C.
Proof.
	intros A B C D E F G.
	intros BetS_A_E_B.
	intros BetS_C_F_D.
	intros OppositeSide_A_EF_D.
	intros Col_A_B_G.
	intros Col_C_D_G.
	intros nCol_E_F_D.
	intros BetS_A_E_G.

	assert (eq E E) as eq_E_E by (reflexivity).
	assert (eq F F) as eq_F_F by (reflexivity).

	pose proof (by_def_Col_from_eq_A_C E F E eq_E_E) as Col_E_F_E.
	pose proof (by_def_Col_from_eq_B_C E F F eq_F_F) as Col_E_F_F.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_E_B) as (_ & _ & neq_A_B).
	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_E_B) as Col_A_E_B.
	pose proof (by_prop_Col_order _ _ _ Col_A_E_B) as (_ & _ & Col_B_A_E & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_F_D) as BetS_D_F_C.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_F_D) as (neq_F_D & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_F_D) as (_ & _ & neq_C_D).
	pose proof (by_prop_neq_symmetric _ _ neq_F_D) as neq_D_F.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_F_D) as Col_C_F_D.
	pose proof (by_prop_Col_order _ _ _ Col_C_F_D) as (_ & _ & _ & Col_C_D_F & _).
	pose proof (by_prop_Col_order _ _ _ Col_C_D_F) as (_ & Col_D_F_C & _ & _ & _).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_E_F_D) as (neq_E_F & _ & _ & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_E_F_D) as (_ & nCol_F_D_E & _ & _ & _).

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_D_F_C Col_E_F_F nCol_E_F_D) as OppositeSide_D_EF_C.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_E_F) as OnRay_EF_F.

	assert (OppositeSide_A_EF_D2 := OppositeSide_A_EF_D).
	destruct OppositeSide_A_EF_D2 as (H & BetS_A_H_D & Col_E_F_H & nCol_E_F_A).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_H_D) as BetS_D_H_A.

	pose proof (by_prop_nCol_order _ _ _ nCol_E_F_A) as (_ & _ & nCol_A_E_F & _ & _).

	pose proof (by_prop_Col_order _ _ _ Col_A_B_G) as (Col_B_A_G & _ & _ & _ & _).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_A_G Col_B_A_E neq_B_A) as Col_A_G_E.
	pose proof (by_prop_Col_order _ _ _ Col_A_G_E) as (Col_G_A_E & _ & _ & Col_A_E_G & _).

	pose proof (by_prop_Col_order _ _ _ Col_C_D_G) as (_ & _ & _ & Col_C_G_D & _).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_D_F Col_C_D_G neq_C_D) as Col_D_F_G.
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_F_G Col_D_F_C neq_D_F) as Col_F_G_C.
	pose proof (by_prop_Col_order _ _ _ Col_F_G_C) as (_ & _ & _ & _ & Col_C_G_F).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_G) as BetS_G_E_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_E_G) as (_ & _ & neq_A_G).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_G_E_A) as (_ & neq_G_E & _).

	pose proof (by_def_OnRay _ _ _ _ BetS_A_E_G BetS_A_E_B) as OnRay_EG_B.

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_E_F Col_A_E_G neq_A_G) as nCol_A_G_F.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_G_F) as (nCol_G_A_F & _ & _ & _ & _).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_G_A_F Col_G_A_E neq_G_E) as nCol_G_E_F.
	pose proof (by_prop_nCol_order _ _ _ nCol_G_E_F) as (nCol_E_G_F & nCol_E_F_G & _ & _ & _).

	pose proof (by_def_Triangle _ _ _ nCol_E_G_F) as Triangle_EGF.
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_G_E_F) as CongA_GEF_GEF.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_GEF_GEF OnRay_EG_B OnRay_EF_F) as CongA_GEF_BEF.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_GEF_BEF) as nCol_B_E_F.

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_E_F) as CongA_BEF_FEB.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_GEF_BEF CongA_BEF_FEB) as CongA_GEF_FEB.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_GEF_FEB) as CongA_FEB_GEF.

	pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_E_F_H Col_E_F_E BetS_D_H_A BetS_G_E_A nCol_E_F_D nCol_E_F_G) as SameSide_D_G_EF.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_D_G_EF) as (SameSide_G_D_EF & _ & _).
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_G_D_EF OppositeSide_D_EF_C) as OppositeSide_G_EF_C.

	destruct OppositeSide_G_EF_C as (R & BetS_G_R_C & Col_E_F_R & _).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_G_R_C) as (_ & _ & neq_G_C).
	pose proof (by_prop_neq_symmetric _ _ neq_G_C) as neq_C_G.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_G_R_C) as Col_G_R_C.
	pose proof (by_prop_Col_order _ _ _ Col_G_R_C) as (_ & _ & Col_C_G_R & _ & _).

	pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_C_G Col_C_G_R Col_C_G_F Col_C_G_D) as Col_R_F_D.
	pose proof (by_prop_Col_order _ _ _ Col_R_F_D) as (Col_F_R_D & _ & _ & _ & _).

	pose proof (by_prop_Col_order _ _ _ Col_E_F_R) as (_ & Col_F_R_E & _ & _ & _).

	pose proof (lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB _ _ _ _ Col_F_R_D Col_F_R_E nCol_F_D_E) as eq_F_R.

	assert (BetS G F C) as BetS_G_F_C by (rewrite eq_F_R; exact BetS_G_R_C).

	pose proof (proposition_16 _ _ _ _ Triangle_EGF BetS_G_F_C) as (LtA_GEF_EFC & _).

	pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_GEF_EFC CongA_FEB_GEF) as LtA_FEB_EFC.

	exact LtA_FEB_EFC.
Qed.

End Euclid.
