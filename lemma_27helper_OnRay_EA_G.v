Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_SameSide.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_OnRay_neq_A_C.
Require Import ProofCheckingEuclid.by_prop_OnRay_orderofpoints_any.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_eq_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.proposition_16.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_27helper_OnRay_EA_G :
	forall A B C D E F G,
	BetS A E B ->
	BetS C F D ->
	OppositeSide A E F D ->
	Col A B G ->
	Col C D G ->
	nCol E F D ->
	OnRay E A G ->
	LtA G E F E F D.
Proof.
	intros A B C D E F G.
	intros BetS_A_E_B.
	intros BetS_C_F_D.
	intros OppositeSide_A_EF_D.
	intros Col_A_B_G.
	intros Col_C_D_G.
	intros nCol_E_F_D.
	intros OnRay_EA_G.

	assert (eq E E) as eq_E_E by (reflexivity).

	pose proof (by_def_Col_from_eq_A_C E F E eq_E_E) as Col_E_F_E.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_B) as BetS_B_E_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_E_B) as (_ & _ & neq_A_B).
	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_E_B) as Col_A_E_B.
	pose proof (by_prop_Col_order _ _ _ Col_A_E_B) as (_ & _ & Col_B_A_E & _ & _).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_F_D) as (_ & _ & neq_C_D).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_F_D) as Col_C_F_D.
	pose proof (by_prop_Col_order _ _ _ Col_C_F_D) as (_ & _ & _ & Col_C_D_F & _).

	pose proof (by_prop_nCol_order _ _ _ nCol_E_F_D) as (nCol_F_E_D & nCol_F_D_E & nCol_D_E_F & nCol_E_D_F & nCol_D_F_E).

	assert (OppositeSide_A_EF_D2 := OppositeSide_A_EF_D).
	destruct OppositeSide_A_EF_D2 as (H & _ & _ & nCol_E_F_A).

	pose proof (by_prop_nCol_order _ _ _ nCol_E_F_A) as (nCol_F_E_A & nCol_F_A_E & nCol_A_E_F & nCol_E_A_F & nCol_A_F_E).

	pose proof (by_prop_Col_order _ _ _ Col_A_B_G) as (Col_B_A_G & _ & _ & _ & _).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_A_G Col_B_A_E neq_B_A) as Col_A_G_E.
	pose proof (by_prop_Col_order _ _ _ Col_A_G_E) as (Col_G_A_E & Col_G_E_A & Col_E_A_G & Col_A_E_G & Col_E_G_A).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_D_G Col_C_D_F neq_C_D) as Col_D_G_F.
	pose proof (by_prop_Col_order _ _ _ Col_D_G_F) as (Col_G_D_F & _ & _ & _ & _).

	pose proof (by_prop_OnRay_neq_A_C _ _ _ OnRay_EA_G) as neq_E_G.

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_E_A_F Col_E_A_G neq_E_G) as nCol_E_G_F.
	pose proof (by_prop_nCol_order _ _ _ nCol_E_G_F) as (nCol_G_E_F & nCol_G_F_E & nCol_F_E_G & nCol_E_F_G & nCol_F_G_E).

	pose proof (by_def_Triangle _ _ _ nCol_E_G_F) as Triangle_EGF.

	(* assert by cases *)
	assert (BetS B E G) as BetS_B_E_G.
	pose proof (by_prop_OnRay_orderofpoints_any _ _ _ OnRay_EA_G) as [BetS_E_G_A | [eq_A_G | BetS_E_A_G]].
	{
		(* case BetS_E_G_A *)
		pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_B_E_A BetS_E_G_A) as BetS_B_E_G.

		exact BetS_B_E_G.
	}
	{
		(* case eq_A_G *)
		pose proof (by_prop_eq_symmetric _ _ eq_A_G) as eq_G_A.
		assert (BetS B E G) as BetS_B_E_G by (rewrite eq_G_A; exact BetS_B_E_A).

		exact BetS_B_E_G.
	}
	{
		(* case BetS_E_A_G *)
		pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_B_E_A BetS_E_A_G) as BetS_B_E_G.

		exact BetS_B_E_G.
	}
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_E_G) as BetS_G_E_B.

	pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_E_F_E Col_E_F_E BetS_A_E_B BetS_G_E_B nCol_E_F_A nCol_E_F_G) as SameSide_A_G_EF.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_A_G_EF) as (SameSide_G_A_EF & _ & _).
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_G_A_EF OppositeSide_A_EF_D) as OppositeSide_G_EF_D.

	destruct OppositeSide_G_EF_D as (P & BetS_G_P_D & Col_E_F_P & _).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_G_P_D) as (_ & _ & neq_G_D).

	pose proof (by_prop_Col_order _ _ _ Col_E_F_P) as (Col_F_E_P & Col_F_P_E & Col_P_E_F & Col_E_P_F & Col_P_F_E).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_G_P_D) as Col_G_P_D.
	pose proof (by_prop_Col_order _ _ _ Col_G_P_D) as (_ & _ & _ & Col_G_D_P & _).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_G_D_P Col_G_D_F neq_G_D) as Col_D_P_F.
	pose proof (by_prop_Col_order _ _ _ Col_D_P_F) as (Col_P_D_F & Col_P_F_D & Col_F_D_P & Col_D_F_P & Col_F_P_D).

	pose proof (lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB _ _ _ _ Col_F_P_D Col_F_P_E nCol_F_D_E) as eq_F_P.
	pose proof (by_prop_eq_symmetric _ _ eq_F_P) as eq_P_F.

	assert (BetS G F D) as BetS_G_F_D by (rewrite <- eq_P_F; exact BetS_G_P_D).

	pose proof (proposition_16 _ _ _ _ Triangle_EGF BetS_G_F_D) as (LtA_GEF_EFD & _).

	exact LtA_GEF_EFD.
Qed.

End Euclid.
