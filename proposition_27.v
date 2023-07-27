Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_Par.
Require Import ProofCheckingEuclid.by_def_Supp.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_distinct.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_eq_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_27helper_BetS_A_E_G.
Require Import ProofCheckingEuclid.lemma_27helper_OnRay_EA_G.
Require Import ProofCheckingEuclid.lemma_angletrichotomy.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_supplements_conga.
Require Import ProofCheckingEuclid.proposition_16.


Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_27 :
	forall A B C D E F,
	BetS A E B ->
	BetS C F D ->
	CongA A E F E F D ->
	OppositeSide A E F D ->
	Par A B C D.
Proof.
	intros A B C D E F.
	intros BetS_A_E_B.
	intros BetS_C_F_D.
	intros CongA_AEF_EFD.
	intros OppositeSide_A_EF_D.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq D D) as eq_D_D by (reflexivity).

	pose proof (by_def_Col_from_eq_A_C A B A eq_A_A) as Col_A_B_A.
	pose proof (by_def_Col_from_eq_B_C C D D eq_D_D) as Col_C_D_D.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_E_B) as (_ & _ & neq_A_B).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_E_B) as (_ & neq_A_E & _).
	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_E_B) as Col_A_E_B.
	pose proof (by_def_Col_from_BetS_A_C_B _ _ _ BetS_A_E_B) as Col_A_B_E.
	pose proof (by_prop_Col_order _ _ _ Col_A_E_B) as (_ & _ & Col_B_A_E & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_F_D) as BetS_D_F_C.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_F_D) as (neq_F_D & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_F_D) as (_ & _ & neq_C_D).
	pose proof (by_prop_neq_symmetric _ _ neq_F_D) as neq_D_F.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_F_D) as Col_C_F_D.
	pose proof (by_prop_Col_order _ _ _ Col_C_F_D) as (_ & _ & _ & Col_C_D_F & _).
	pose proof (by_prop_Col_order _ _ _ Col_C_D_F) as (_ & Col_D_F_C & _ & _ & _).

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_AEF_EFD) as CongA_EFD_AEF.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_AEF_EFD) as nCol_E_F_D.

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_E_F_D) as CongA_EFD_DFE.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_AEF_EFD CongA_EFD_DFE) as CongA_AEF_DFE.

	pose proof (by_prop_CongA_distinct _ _ _ _ _ _ CongA_EFD_AEF) as (neq_E_F & _ & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_E_F) as neq_F_E.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_E_F) as OnRay_EF_F.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_F_E) as OnRay_FE_E.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_EF_F BetS_A_E_B) as Supp_AEF_FEB.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_FE_E BetS_D_F_C) as Supp_DFE_EFC.
	pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_AEF_DFE Supp_AEF_FEB Supp_DFE_EFC) as CongA_FEB_EFC.

	assert (OppositeSide_A_EF_D2 := OppositeSide_A_EF_D).
	destruct OppositeSide_A_EF_D2 as (H & BetS_A_H_D & Col_E_F_H & nCol_E_F_A).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_H_D) as (_ & _ & neq_A_D).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_H_D) as (neq_H_D & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_A_D) as neq_D_A.
	pose proof (by_prop_neq_symmetric _ _ neq_H_D) as neq_D_H.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_H_D) as Col_A_H_D.
	pose proof (by_prop_Col_order _ _ _ Col_A_H_D) as (_ & _ & _ & _ & Col_D_H_A).
	pose proof (by_prop_Col_order _ _ _ Col_A_H_D) as (_ & _ & Col_D_A_H & _ & _).

	pose proof (by_prop_Col_order _ _ _ Col_E_F_H) as (Col_F_E_H & Col_F_H_E & Col_H_E_F & Col_E_H_F & Col_H_F_E).

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_E_F_A) as n_Col_E_F_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_E_F_A) as (nCol_F_E_A & nCol_F_A_E & nCol_A_E_F & nCol_E_A_F & nCol_A_F_E).
	pose proof (by_def_Triangle _ _ _ nCol_E_A_F) as Triangle_EAF.

	assert (~ Meet A B C D) as n_Meet_A_B_C_D.
	{
		intro Meet_A_B_C_D.

		assert (Meet_A_B_C_D2 := Meet_A_B_C_D).
		destruct Meet_A_B_C_D2 as (G & _ & _ & Col_A_B_G & Col_C_D_G).

		pose proof (by_prop_Col_order _ _ _ Col_A_B_G) as (Col_B_A_G & _ & _ & _ & _).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_A_G Col_B_A_E neq_B_A) as Col_A_G_E.
		pose proof (by_prop_Col_order _ _ _ Col_A_G_E) as (Col_G_A_E & Col_G_E_A & Col_E_A_G & Col_A_E_G & Col_E_G_A).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_D_G Col_C_D_F neq_C_D) as Col_D_G_F.

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_D_F Col_C_D_G neq_C_D) as Col_D_F_G.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_F_G Col_D_F_C neq_D_F) as Col_F_G_C.
		pose proof (by_prop_Col_order _ _ _ Col_F_G_C) as (Col_G_F_C & Col_G_C_F & Col_C_F_G & Col_F_C_G & Col_C_G_F).


		assert (~ BetS A E G) as n_BetS_A_E_G.
		{
			intro BetS_A_E_G.

			pose proof (lemma_27helper_BetS_A_E_G _ _ _ _ _ _ _ BetS_A_E_B BetS_C_F_D OppositeSide_A_EF_D Col_A_B_G Col_C_D_G nCol_E_F_D BetS_A_E_G) as (LtA_GEF_EFC & CongA_FEB_GEF).

			pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_GEF_EFC CongA_FEB_EFC) as LtA_GEF_FEB.
			pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_GEF_FEB CongA_FEB_GEF) as LtA_FEB_FEB.
			pose proof (lemma_angletrichotomy _ _ _ _ _ _ LtA_FEB_FEB) as n_LtA_FEB_FEB.

			contradict LtA_FEB_FEB.
			exact n_LtA_FEB_FEB.
		}

		assert (~ OnRay E A G) as n_OnRay_EA_G.
		{
			intro OnRay_EA_G.

			pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_EA_G) as OnRay_EG_A.
			pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_EFD_AEF OnRay_EA_G OnRay_EF_F) as CongA_EFD_GEF.

			pose proof (lemma_27helper_OnRay_EA_G _ _ _ _ _ _ _ BetS_A_E_B BetS_C_F_D OppositeSide_A_EF_D Col_A_B_G Col_C_D_G nCol_E_F_D OnRay_EA_G) as LtA_GEF_EFD.
			pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_GEF_EFD CongA_EFD_GEF) as LtA_EFD_EFD.
			pose proof (lemma_angletrichotomy _ _ _ _ _ _ LtA_EFD_EFD) as n_LtA_EFD_EFD.

			contradict LtA_EFD_EFD.
			exact n_LtA_EFD_EFD.
		}

		assert (~ eq A G) as n_eq_A_G.
		{
			intros eq_A_G.

			assert (Col D A F) as Col_D_A_F by (rewrite eq_A_G; exact Col_D_G_F).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_A_F Col_D_A_H neq_D_A) as Col_A_F_H.
			pose proof (by_prop_Col_order _ _ _ Col_A_F_H) as (Col_F_A_H & Col_F_H_A & Col_H_A_F & Col_A_H_F & Col_H_F_A).

			pose proof (lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB _ _ _ _ Col_F_H_A Col_F_H_E nCol_F_A_E) as eq_F_H.
			pose proof (by_prop_eq_symmetric _ _ eq_F_H) as eq_H_F.

			assert (BetS A F D) as BetS_A_F_D by (rewrite <- eq_H_F; exact BetS_A_H_D).

			pose proof (proposition_16 _ _ _ _ Triangle_EAF BetS_A_F_D) as (LtA_AEF_EFD & _).
			pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_AEF_EFD CongA_EFD_AEF) as LtA_EFD_EFD.
			pose proof (lemma_angletrichotomy _ _ _ _ _ _ LtA_EFD_EFD) as n_LtA_EFD_EFD.

			contradict LtA_EFD_EFD.
			exact n_LtA_EFD_EFD.
		}
		assert (neq_A_G := n_eq_A_G).

		assert (~ eq E G) as n_eq_E_G.
		{
			intros eq_E_G.

			assert (Col C D E) as Col_C_D_E by (rewrite eq_E_G; exact Col_C_D_G).

			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_D_E Col_C_D_F neq_C_D) as Col_D_E_F.
			pose proof (by_prop_Col_order _ _ _ Col_D_E_F) as (_ & Col_E_F_D & _ & _ & _).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_E_F_D Col_E_F_H neq_E_F) as Col_F_D_H.
			pose proof (by_prop_Col_order _ _ _ Col_F_D_H) as (_ & Col_D_H_F & _ & _ & _).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_H_F Col_D_H_A neq_D_H) as Col_H_F_A.
			pose proof (by_prop_Col_order _ _ _ Col_H_F_A) as (Col_F_H_A & Col_F_A_H & Col_A_H_F & Col_H_A_F & Col_A_F_H).

			pose proof (lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB _ _ _ _ Col_F_H_A Col_F_H_E nCol_F_A_E) as eq_F_H.
			pose proof (by_prop_eq_symmetric _ _ eq_F_H) as eq_H_F.

			assert (Col A F D) as Col_A_F_D by (rewrite <-eq_H_F; exact Col_A_H_D).

			pose proof (by_prop_Col_order _ _ _ Col_A_F_D) as (_ & _ & _ & _ & Col_D_F_A).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_F_A Col_D_F_C neq_D_F) as Col_F_A_C.
			pose proof (by_prop_Col_order _ _ _ Col_F_A_C) as (Col_A_F_C & Col_A_C_F & Col_C_F_A & Col_F_C_A & Col_C_A_F).

			assert (nCol F A G) as nCol_F_A_G by (rewrite <- eq_E_G; exact nCol_F_A_E).

			pose proof (lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB _ _ _ _ Col_F_C_A Col_F_C_G nCol_F_A_G) as eq_F_C.
			pose proof (by_prop_eq_symmetric _ _ eq_F_C) as eq_C_F.

			assert (Col A C D) as Col_A_C_D by (rewrite eq_C_F; exact Col_A_F_D).
			pose proof (by_prop_Col_order _ _ _ Col_A_C_D) as (_ & Col_C_D_A & _ & _ & _).
			assert (Col F D A) as Col_F_D_A by (rewrite <- eq_C_F; exact Col_C_D_A).
			assert (Col F D E) as Col_F_D_E by (rewrite <- eq_C_F; exact Col_C_D_E).
			pose proof (by_prop_Col_order _ _ _ Col_F_D_E) as (Col_D_F_E & _ & _ & _ & _).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_F_E Col_D_F_A neq_D_F) as Col_F_E_A.
			pose proof (by_prop_Col_order _ _ _ Col_F_E_A) as (Col_E_F_A & _ & _ & _ & _).

			contradict Col_E_F_A.
			exact n_Col_E_F_A.
		}
		assert (neq_E_G := n_eq_E_G).


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
			contradict eq_A_G.
			exact neq_A_G.
		}
		{
			(* case eq_E_G *)
			contradict eq_E_G.
			exact neq_E_G.
		}
		{
			(* case BetS_E_A_G *)
			pose proof (by_prop_BetS_notequal _ _ _ BetS_E_A_G) as (_ & neq_E_A & _).

			pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_E_A_G neq_E_A) as OnRay_EA_G.

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
			pose proof (by_prop_BetS_notequal _ _ _ BetS_E_G_A) as (_ & _ & neq_E_A).

			pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_E_G_A neq_E_A) as OnRay_EA_G.

			contradict OnRay_EA_G.
			exact n_OnRay_EA_G.
		}

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_A_E_B Col_C_F_D neq_A_B neq_C_D neq_A_E neq_F_D n_Meet_A_B_C_D BetS_A_H_D Col_E_F_H) as BetS_E_H_F.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_H_F) as BetS_F_H_E.

	pose proof (by_def_Par _ _ _ _ _ _ _ _ _ neq_A_B neq_C_D Col_A_B_A Col_A_B_E neq_A_E Col_C_D_F Col_C_D_D neq_F_D n_Meet_A_B_C_D BetS_A_H_D BetS_F_H_E) as Par_AB_CD.

	exact Par_AB_CD.
Qed.

End Euclid.
