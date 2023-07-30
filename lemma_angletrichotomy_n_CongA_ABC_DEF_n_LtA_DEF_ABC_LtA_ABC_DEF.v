Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_def_LtA.
Require Import ProofCheckingEuclid.by_def_OnRay.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_OnRay_impliescollinear.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_outerconnectivity.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_sameside_onray_EFAC_BFG_EGAC.
Require Import ProofCheckingEuclid.proposition_23C.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_angletrichotomy_n_CongA_ABC_DEF_n_LtA_DEF_ABC_LtA_ABC_DEF :
	forall A B C D E F,
	nCol A B C ->
	nCol D E F ->
	~ CongA A B C D E F ->
	~ LtA D E F A B C ->
	LtA A B C D E F.
Proof.
	intros A B C D E F.
	intros nCol_A_B_C.
	intros nCol_D_E_F.
	intros n_CongA_ABC_DEF.
	intros n_LtA_DEF_ABC.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).

	pose proof (cn_congruencereflexive B A) as Cong_BA_BA.

	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_C) as n_Col_A_B_C.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_A_B_C) as CongA_ABC_ABC.

	pose proof (proposition_23C _ _ _ _ _ _ neq_B_A nCol_D_E_F nCol_B_A_C) as (G & J & OnRay_BA_J & CongA_GBJ_DEF & SameSide_G_C_BA).

	pose proof (cn_congruencereflexive A G) as Cong_AG_AG.
	pose proof (cn_congruencereflexive B G) as Cong_BG_BG.

	assert (SameSide_G_C_BA2 := SameSide_G_C_BA).
	destruct SameSide_G_C_BA2 as (_ & _ & _ & _ & _ & _ & _ & nCol_B_A_G & _).
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_B_A_G) as n_Col_B_A_G.

	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_A_G) as (_ & neq_A_G & neq_B_G & _ & neq_G_A & neq_G_B).
	pose proof (by_prop_nCol_order _ _ _ nCol_B_A_G) as (nCol_A_B_G & nCol_A_G_B & nCol_G_B_A & nCol_B_G_A & nCol_G_A_B).
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_A_B_G) as CongA_ABG_ABG.
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_G) as n_Col_A_B_G.

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_B_G) as CongA_ABG_GBA.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_G_B_A) as CongA_GBA_ABG.

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_GBJ_DEF) as CongA_DEF_GBJ.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_BA_J) as OnRay_BJ_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_A) as OnRay_BA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_C) as OnRay_BC_C.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_G) as OnRay_BG_G.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_DEF_GBJ OnRay_BG_G OnRay_BJ_A) as CongA_DEF_GBA.

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_DEF_GBA) as CongA_GBA_DEF.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABG_GBA CongA_GBA_DEF) as CongA_ABG_DEF.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ABG_DEF) as CongA_DEF_ABG.

	pose proof (lemma_extension _ _ _ _ neq_G_A neq_G_A) as (P & BetS_G_A_P & Cong_AP_GA).
	pose proof (by_def_Col_from_eq_B_C B A A eq_A_A) as Col_B_A_A.

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_G_C_BA) as (SameSide_C_G_BA & _ & _).
	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_G_A_P Col_B_A_A nCol_B_A_G) as OppositeSide_G_BA_P.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_C_G_BA OppositeSide_G_BA_P) as OppositeSide_C_BA_P.

	destruct OppositeSide_C_BA_P as (R & BetS_C_R_P & Col_B_A_R & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_R_P) as BetS_P_R_C.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_R_P) as (_ & _ & neq_C_P).
	pose proof (by_prop_neq_symmetric _ _ neq_C_P) as neq_P_C.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_G_A_P) as Col_G_A_P.
	pose proof (by_prop_Col_order _ _ _ Col_G_A_P) as (Col_A_G_P & Col_A_P_G & Col_P_G_A & Col_G_P_A & Col_P_A_G).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_R_P) as Col_C_R_P.
	pose proof (by_prop_Col_order _ _ _ Col_C_R_P) as (Col_R_C_P & Col_R_P_C & Col_P_C_R & Col_C_P_R & Col_P_R_C).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_G_A_P) as (neq_A_P & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_A_P) as neq_P_A.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_G_A_P) as (_ & _ & neq_G_P).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_A_P) as BetS_P_A_G.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_P_A_G) as (_ & _ & neq_P_G).

	(* assert by cases *)
	assert (LtA A B C D E F) as LtA_ABC_DEF.
	assert (OppositeSide G B C A \/ ~ OppositeSide G B C A) as [OppositeSide_G_BC_A | n_OppositeSide_G_BC_A] by (apply Classical_Prop.classic).
	{
		(* case OppositeSide_G_BC_A *)

		destruct OppositeSide_G_BC_A as (H & BetS_G_H_A & Col_B_C_H & nCol_B_C_G).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_H_A) as BetS_A_H_G.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_G_H_A) as (neq_H_A & neq_G_H & _).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_A_H_G) as (neq_H_G & neq_A_H & _).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_H_G) as Col_A_H_G.

		pose proof (by_prop_Col_order _ _ _ Col_A_H_G) as (Col_H_A_G & Col_H_G_A & Col_G_A_H & Col_A_G_H & Col_G_H_A).
		pose proof (by_prop_Col_order _ _ _ Col_B_C_H) as (Col_C_B_H & Col_C_H_B & Col_H_B_C & Col_B_H_C & Col_H_C_B).

		pose proof (by_prop_nCol_distinct _ _ _ nCol_B_C_G) as (_ & neq_C_G & _ & _ & neq_G_C & _).
		pose proof (by_prop_nCol_order _ _ _ nCol_B_C_G) as (nCol_C_B_G & nCol_C_G_B & nCol_G_B_C & nCol_B_G_C & nCol_G_C_B).

		pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_G_A_B Col_G_A_H neq_G_H) as nCol_G_H_B.
		pose proof (by_prop_nCol_distinct _ _ _ nCol_G_H_B) as (_ & neq_H_B & _ & _ & neq_B_H & _).

		pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_C_A Col_B_C_H neq_B_H) as nCol_B_H_A.
		pose proof (by_prop_nCol_order _ _ _ nCol_B_H_A) as (nCol_H_B_A & nCol_H_A_B & nCol_A_B_H & nCol_B_A_H & nCol_A_H_B).

		pose proof (by_def_n_Col_from_nCol _ _ _ nCol_B_H_A) as n_Col_B_H_A.

		pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_H_B_A) as CongA_HBA_ABH.
		pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_B_H) as CongA_ABH_HBA.

		pose proof (by_prop_CongA_reflexive _ _ _ nCol_A_B_H) as CongA_ABH_ABH.
		pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_A_H_G OnRay_BA_A OnRay_BG_G CongA_ABH_ABH) as LtA_ABH_ABG.
		pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_ABH_ABG CongA_GBA_ABG) as LtA_ABH_GBA.


		pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_ABH_GBA CongA_HBA_ABH) as LtA_HBA_GBA.
		pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_HBA_GBA CongA_DEF_GBA) as LtA_HBA_DEF.
		pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_HBA_DEF CongA_ABH_HBA) as LtA_ABH_DEF.

		pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_A_H_G neq_A_G) as OnRay_AG_H.

		pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_C_G_BA Col_B_A_A OnRay_AG_H) as SameSide_C_H_BA.

		assert (~ BetS C B H) as n_BetS_C_B_H.
		{
			intro BetS_C_B_H.

			pose proof (by_def_Col_from_eq_A_C B A B eq_B_B) as Col_B_A_B.
			pose proof (by_def_OppositeSide _ _ _ _ _ BetS_C_B_H Col_B_A_B nCol_B_A_C) as OppositeSide_C_BA_H.
			pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_C_BA_H) as OppositeSide_H_BA_C.
			pose proof (lemma_planeseparation _ _ _ _ _ SameSide_C_H_BA OppositeSide_H_BA_C) as OppositeSide_C_BA_C.

			destruct OppositeSide_C_BA_C as (M & BetS_C_M_C & Col_B_A_M & _).
			pose proof (axiom_betweennessidentity C M) as n_BetS_C_M_C.

			contradict BetS_C_M_C.
			exact n_BetS_C_M_C.
		}


		(* assert by cases *)
		assert (OnRay B C H) as OnRay_BC_H.
		destruct Col_B_C_H as [eq_B_C | [eq_B_H | [eq_C_H | [BetS_C_B_H | [BetS_B_C_H | BetS_B_H_C]]]]].
		{
			(* case eq_B_C *)
			pose proof (by_def_Col_from_eq_B_C A B C eq_B_C) as Col_A_B_C.

			contradict Col_A_B_C.
			exact n_Col_A_B_C.
		}
		{
			(* case eq_B_H *)
			pose proof (by_def_Col_from_eq_A_B B H A eq_B_H) as Col_B_H_A.

			contradict Col_B_H_A.
			exact n_Col_B_H_A.
		}
		{
			(* case eq_C_H *)

			pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_H) as OnRay_BH_H.
			assert (OnRay B C H) as OnRay_BC_H by (rewrite eq_C_H; exact OnRay_BH_H).

			exact OnRay_BC_H.
		}
		{
			(* case BetS_C_B_H *)

			contradict BetS_C_B_H.
			exact n_BetS_C_B_H.
		}
		{
			(* case BetS_B_C_H *)
			pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_C_H neq_B_C) as OnRay_BC_H.

			exact OnRay_BC_H.
		}
		{
			(* case BetS_B_H_C *)
			pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_B_H_C neq_B_C) as OnRay_BC_H.

			exact OnRay_BC_H.
		}
		pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_ABC_ABC OnRay_BA_A OnRay_BC_H) as CongA_ABC_ABH.
		pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_ABH_DEF CongA_ABC_ABH) as LtA_ABC_DEF.

		exact LtA_ABC_DEF.
	}
	{
		(* case n_OppositeSide_G_BC_A *)

		(* assert by cases *)
		assert (LtA A B C D E F) as LtA_ABC_DEF.
		destruct Col_B_A_R as [eq_B_A | [eq_B_R | [eq_A_R | [BetS_A_B_R | [BetS_B_A_R | BetS_B_R_A]]]]].
		{
			(* case eq_B_A *)

			contradict eq_B_A.
			exact neq_B_A.
		}
		{
			(* case eq_B_R *)
			assert (Col C B P) as Col_C_B_P by (rewrite eq_B_R; exact Col_C_R_P).
			pose proof (by_prop_Col_order _ _ _ Col_C_B_P) as (Col_B_C_P & Col_B_P_C & Col_P_C_B & Col_C_P_B & Col_P_B_C).

			pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_G_A_B Col_G_A_P neq_G_P) as nCol_G_P_B.
			pose proof (by_prop_nCol_order _ _ _ nCol_G_P_B) as (nCol_P_G_B & nCol_P_B_G & nCol_B_G_P & nCol_G_B_P & nCol_B_P_G).

			pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_P_B_G Col_P_B_C neq_P_C) as nCol_P_C_G.
			pose proof (by_prop_nCol_order _ _ _ nCol_P_C_G) as (nCol_C_P_G & nCol_C_G_P & nCol_G_P_C & nCol_P_G_C & nCol_G_C_P).

			pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_C_R_P BetS_G_A_P nCol_C_P_G) as (Q & BetS_C_Q_A & BetS_G_Q_R).

			assert (BetS G Q B) as BetS_G_Q_B by (rewrite eq_B_R; exact BetS_G_Q_R).
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_Q_B) as BetS_B_Q_G.
			pose proof (by_prop_BetS_notequal _ _ _ BetS_B_Q_G) as (_ & neq_B_Q & _).
			pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_Q) as OnRay_BQ_Q.

			pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_Q_G neq_B_Q) as OnRay_BQ_G.

			pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_BQ_G) as OnRay_BG_Q.
			pose proof (cn_congruencereflexive A Q) as Cong_AQ_AQ.
			pose proof (cn_congruencereflexive B Q) as Cong_BQ_BQ.
			pose proof (by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_BA_A OnRay_BG_Q OnRay_BA_A OnRay_BQ_Q Cong_BA_BA Cong_BQ_BQ Cong_AQ_AQ nCol_A_B_G) as CongA_ABG_ABQ.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_Q_A) as BetS_A_Q_C.
			pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_A_Q_C OnRay_BA_A OnRay_BC_C CongA_ABG_ABQ) as LtA_ABG_ABC.
			pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_ABG_ABC CongA_DEF_ABG) as LtA_DEF_ABC.

			contradict LtA_DEF_ABC.
			exact n_LtA_DEF_ABC.
		}
		{
			(* case eq_A_R *)
			assert (BetS P A C) as BetS_P_A_C by (rewrite eq_A_R; exact BetS_P_R_C).

			assert (~ ~ LtA A B C D E F) as n_n_LtA_ABC_DEF.
			{
				intro n_LtA_ABC_DEF.


				assert (~ BetS A G C) as n_BetS_A_G_C.
				{
					intro BetS_A_G_C.

					pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_A_G_C OnRay_BA_A OnRay_BC_C CongA_ABG_ABG) as LtA_ABG_ABC.
					pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_ABG_ABC CongA_DEF_ABG) as LtA_DEF_ABC.

					contradict LtA_DEF_ABC.
					exact n_LtA_DEF_ABC.
				}


				assert (~ BetS A C G) as n_BetS_A_C_G.
				{
					intro BetS_A_C_G.

					pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_A_C_G OnRay_BA_A OnRay_BG_G CongA_ABC_ABC) as LtA_ABC_ABG.
					pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_ABC_ABG CongA_DEF_ABG) as LtA_ABC_DEF.

					contradict LtA_ABC_DEF.
					exact n_LtA_ABC_DEF.
				}

				pose proof (lemma_outerconnectivity _ _ _ _ BetS_P_A_C BetS_P_A_G n_BetS_A_C_G n_BetS_A_G_C) as eq_C_G.
				assert (CongA A B G A B C) as CongA_ABG_ABC by (rewrite <- eq_C_G; exact CongA_ABC_ABC).
				pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ABG_ABC) as CongA_ABC_ABG.
				pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_ABG CongA_ABG_DEF) as CongA_ABC_DEF.

				contradict CongA_ABC_DEF.
				exact n_CongA_ABC_DEF.
			}
			assert (LtA_ABC_DEF := n_n_LtA_ABC_DEF).
			apply Classical_Prop.NNPP in LtA_ABC_DEF.

			exact LtA_ABC_DEF.
		}
		{
			(* case BetS_A_B_R *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_R) as BetS_R_B_A.
			pose proof (by_prop_BetS_notequal _ _ _ BetS_A_B_R) as (_ & _& neq_A_R).
			pose proof (by_prop_neq_symmetric _ _ neq_A_R) as neq_R_A.

			pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_B_R) as Col_A_B_R.
			pose proof (by_prop_Col_order _ _ _ Col_A_B_R) as (Col_B_A_R & Col_B_R_A & Col_R_A_B & Col_A_R_B & Col_R_B_A).

			pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_B_C Col_A_B_R neq_A_R) as nCol_A_R_C.
			pose proof (by_prop_nCol_order _ _ _ nCol_A_R_C) as (nCol_R_A_C & nCol_R_C_A & nCol_C_A_R & nCol_A_C_R & nCol_C_R_A).

			pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_C_R_A Col_C_R_P neq_C_P) as nCol_C_P_A.
			pose proof (by_prop_nCol_order _ _ _ nCol_C_P_A) as (nCol_P_C_A & nCol_P_A_C & nCol_A_C_P & nCol_C_A_P & nCol_A_P_C).

			pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_A_B_R BetS_C_R_P nCol_C_P_A) as (M & BetS_A_M_P & BetS_C_B_M).
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_M_P) as BetS_P_M_A.
			pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_P_M_A BetS_P_A_G) as BetS_M_A_G.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_M_A_G) as BetS_G_A_M.

			pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_P_M_A BetS_P_A_G) as BetS_P_M_G.
			pose proof (by_prop_BetS_notequal _ _ _ BetS_P_M_G) as (neq_M_G & _ & _).
			pose proof (by_prop_BetS_notequal _ _ _ BetS_C_B_M) as (neq_B_M & _ & neq_C_M).
			pose proof (by_prop_neq_symmetric _ _ neq_M_G) as neq_G_M.
			pose proof (by_prop_neq_symmetric _ _ neq_C_M) as neq_M_C.

			pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_M_P) as Col_A_M_P.
			pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_G_A_M) as Col_G_A_M.
			pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_P_M_G) as Col_P_M_G.
			pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_B_M) as Col_C_B_M.

			pose proof (by_prop_Col_order _ _ _ Col_A_M_P) as (Col_M_A_P & Col_M_P_A & Col_P_A_M & Col_A_P_M & Col_P_M_A).
			pose proof (by_prop_Col_order _ _ _ Col_G_A_M) as (Col_A_G_M & Col_A_M_G & Col_M_G_A & Col_G_M_A & Col_M_A_G).
			pose proof (by_prop_Col_order _ _ _ Col_P_M_G) as (Col_M_P_G & Col_M_G_P & Col_G_P_M & Col_P_G_M & Col_G_M_P).
			pose proof (by_prop_Col_order _ _ _ Col_C_B_M) as (Col_B_C_M & Col_B_M_C & Col_M_C_B & Col_C_M_B & Col_M_B_C).

			pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_C_B_A Col_C_B_M neq_C_M) as nCol_C_M_A.
			pose proof (by_prop_nCol_order _ _ _ nCol_C_M_A) as (nCol_M_C_A & nCol_M_A_C & nCol_A_C_M & nCol_C_A_M & nCol_A_M_C).

			pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_M_C Col_A_M_G neq_A_G) as nCol_A_G_C.
			pose proof (by_prop_nCol_order _ _ _ nCol_A_G_C) as (nCol_G_A_C & nCol_G_C_A & nCol_C_A_G & nCol_A_C_G & nCol_C_G_A).

			pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_G_A_C Col_G_A_M neq_G_M) as nCol_G_M_C.
			pose proof (by_prop_nCol_order _ _ _ nCol_G_M_C) as (nCol_M_G_C & nCol_M_C_G & nCol_C_G_M & nCol_G_C_M & nCol_C_M_G).

			pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_C_B_M BetS_G_A_M nCol_C_M_G) as (Q & BetS_C_Q_A & BetS_G_Q_B).

			pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_Q_B) as BetS_B_Q_G.
			pose proof (by_prop_BetS_notequal _ _ _ BetS_B_Q_G) as (_ & neq_B_Q & _).
			pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_Q) as OnRay_BQ_Q.

			pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_Q_G neq_B_Q) as OnRay_BQ_G.

			pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_BQ_G) as OnRay_BG_Q.
			pose proof (cn_congruencereflexive A Q) as Cong_AQ_AQ.
			pose proof (cn_congruencereflexive B Q) as Cong_BQ_BQ.
			pose proof (by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_BA_A OnRay_BG_Q OnRay_BA_A OnRay_BQ_Q Cong_BA_BA Cong_BQ_BQ Cong_AQ_AQ nCol_A_B_G) as CongA_ABG_ABQ.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_Q_A) as BetS_A_Q_C.
			pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_A_Q_C OnRay_BA_A OnRay_BC_C CongA_ABG_ABQ) as LtA_ABG_ABC.
			pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_ABG_ABC CongA_DEF_ABG) as LtA_DEF_ABC.

			contradict LtA_DEF_ABC.
			exact n_LtA_DEF_ABC.
		}
		{
			(* case BetS_B_A_R *)
			pose proof (by_prop_BetS_notequal _ _ _ BetS_B_A_R) as (neq_A_R & _ & neq_B_R).
			pose proof (by_prop_neq_symmetric _ _ neq_B_R) as neq_R_B.

			pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_A_R) as Col_B_A_R.
			pose proof (by_prop_Col_order _ _ _ Col_B_A_R) as (Col_A_B_R & Col_A_R_B & Col_R_B_A & Col_B_R_A & Col_R_A_B).

			pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_A_C Col_B_A_R neq_B_R) as nCol_B_R_C.
			pose proof (by_prop_nCol_order _ _ _ nCol_B_R_C) as (nCol_R_B_C & nCol_R_C_B & nCol_C_B_R & nCol_B_C_R & nCol_C_R_B).

			pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_C_R_B Col_C_R_P neq_C_P) as nCol_C_P_B.
			pose proof (by_prop_nCol_order _ _ _ nCol_C_P_B) as (nCol_P_C_B & nCol_P_B_C & nCol_B_C_P & nCol_C_B_P & nCol_B_P_C).


			pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_B_A_R BetS_P_R_C nCol_P_C_B) as (Q & BetS_B_Q_C & BetS_P_A_Q).

			pose proof (by_prop_BetS_notequal _ _ _ BetS_B_Q_C) as (neq_Q_C & neq_B_Q & _).

			pose proof (by_def_Col_from_BetS_A_C_B _ _ _ BetS_B_Q_C) as Col_B_C_Q.
			pose proof (by_prop_Col_order _ _ _ Col_B_C_Q) as (Col_C_B_Q & Col_C_Q_B & Col_Q_B_C & Col_B_Q_C & Col_Q_C_B).

			assert (~ eq G Q) as n_eq_G_Q.
			{
				intro eq_G_Q.

				assert (BetS B G C) as BetS_B_G_C by (rewrite eq_G_Q; exact BetS_B_Q_C).
				pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_B_G_C neq_B_C) as OnRay_BC_G.

				pose proof (by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_BA_A OnRay_BG_G OnRay_BA_A OnRay_BC_G Cong_BA_BA Cong_BG_BG Cong_AG_AG nCol_A_B_G) as CongA_ABG_ABC.
				pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ABG_ABC) as CongA_ABC_ABG.
				pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_ABG CongA_ABG_DEF) as CongA_ABC_DEF.

				contradict CongA_ABC_DEF.
				exact n_CongA_ABC_DEF.
			}
			assert (neq_G_Q := n_eq_G_Q).

			pose proof (by_def_OnRay _ _ _ _ BetS_P_A_G BetS_P_A_Q) as OnRay_AG_Q.
			pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_AG_Q) as Col_A_G_Q.
			pose proof (by_prop_Col_order _ _ _ Col_A_G_Q) as (Col_G_A_Q & Col_G_Q_A & Col_Q_A_G & Col_A_Q_G & Col_Q_G_A).

			pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_G_A_B Col_G_A_Q neq_G_Q) as nCol_G_Q_B.
			pose proof (by_prop_nCol_order _ _ _ nCol_G_Q_B) as (nCol_Q_G_B & nCol_Q_B_G & nCol_B_G_Q & nCol_G_B_Q & nCol_B_Q_G).

			pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_Q_G Col_B_Q_C neq_B_C) as nCol_B_C_G.
			pose proof (by_prop_nCol_order _ _ _ nCol_B_C_G) as (nCol_C_B_G & nCol_C_G_B & nCol_G_B_C & nCol_B_G_C & nCol_G_C_B).

			assert (~ BetS A Q G) as n_BetS_A_Q_G.
			{
				intro BetS_A_Q_G.

				pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_Q_G) as BetS_G_Q_A.
				pose proof (by_def_OppositeSide _ _ _ _ _ BetS_G_Q_A Col_B_C_Q nCol_B_C_G) as OppositeSide_G_BC_A.

				contradict OppositeSide_G_BC_A.
				exact n_OppositeSide_G_BC_A.
			}


			pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_B_Q_C neq_B_C) as OnRay_BC_Q.


			assert (~ BetS A G Q) as n_BetS_A_G_Q.
			{
				intro BetS_A_G_Q.

				pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_A_G_Q OnRay_BA_A OnRay_BC_Q CongA_ABG_ABG) as LtA_ABG_ABC.
				pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_ABG_ABC CongA_DEF_ABG) as LtA_DEF_ABC.

				contradict LtA_DEF_ABC.
				exact n_LtA_DEF_ABC.
			}

			pose proof (lemma_outerconnectivity _ _ _ _ BetS_P_A_G BetS_P_A_Q n_BetS_A_G_Q n_BetS_A_Q_G) as eq_G_Q.

			contradict eq_G_Q.
			exact neq_G_Q.
		}
		{
			(* case BetS_B_R_A *)
			pose proof (by_prop_BetS_notequal _ _ _ BetS_B_R_A) as (neq_R_A & neq_B_R & _).

			pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_B_R_A neq_B_A) as OnRay_BA_R.
			pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_BA_R) as Col_B_A_R.
			pose proof (by_prop_Col_order _ _ _ Col_B_A_R) as (Col_A_B_R & Col_A_R_B & Col_R_B_A & Col_B_R_A & Col_R_A_B).

			pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_G_A_B Col_G_A_P neq_G_P) as nCol_G_P_B.
			pose proof (by_prop_nCol_order _ _ _ nCol_G_P_B) as (nCol_P_G_B & nCol_P_B_G & nCol_B_G_P & nCol_G_B_P & nCol_B_P_G).

			pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_B_R_A BetS_P_A_G nCol_P_G_B) as (Q & BetS_B_Q_G & BetS_P_R_Q).

			pose proof (by_prop_BetS_notequal _ _ _ BetS_B_Q_G) as (neq_Q_G & _ & _).
			pose proof (by_prop_BetS_notequal _ _ _ BetS_B_Q_G) as (_ & neq_B_Q & _).

			pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_B_Q_G neq_B_G) as OnRay_BG_Q.
			pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_Q_G neq_B_Q) as OnRay_BQ_G.

			pose proof (by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_BA_A OnRay_BG_G OnRay_BA_A OnRay_BQ_G Cong_BA_BA Cong_BG_BG Cong_AG_AG nCol_A_B_G) as CongA_ABG_ABQ.

			assert (~ BetS R Q C) as n_BetS_R_Q_C.
			{
				intro BetS_R_Q_C.

				pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_R_Q_C OnRay_BA_R OnRay_BC_C CongA_ABG_ABQ) as LtA_ABG_ABC.
				pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_ABG_ABC CongA_DEF_ABG) as LtA_DEF_ABC.

				contradict LtA_DEF_ABC.
				exact n_LtA_DEF_ABC.
			}

			assert (~ ~ LtA A B C D E F) as n_n_LtA_ABC_DEF.
			{
				intro n_LtA_ABC_DEF.

				assert (~ BetS R C Q) as n_BetS_R_C_Q.
				{
					intro BetS_R_C_Q.

					pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_R_C_Q OnRay_BA_R OnRay_BG_Q CongA_ABC_ABC) as LtA_ABC_ABG.
					pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_ABC_ABG CongA_DEF_ABG) as LtA_ABC_DEF.
					contradict LtA_ABC_DEF.
					exact n_LtA_ABC_DEF.
				}

				pose proof (lemma_outerconnectivity _ _ _ _ BetS_P_R_Q BetS_P_R_C n_BetS_R_Q_C n_BetS_R_C_Q) as eq_Q_C.
				assert (OnRay B C G) as OnRay_BC_G by (rewrite <- eq_Q_C; exact OnRay_BQ_G).

				pose proof (by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_BA_A OnRay_BC_G OnRay_BA_A OnRay_BG_G Cong_BA_BA Cong_BG_BG Cong_AG_AG nCol_A_B_C) as CongA_ABC_ABG.
				pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_ABG CongA_ABG_DEF) as CongA_ABC_DEF.

				contradict CongA_ABC_DEF.
				exact n_CongA_ABC_DEF.
			}
			assert (LtA_ABC_DEF := n_n_LtA_ABC_DEF).
			apply Classical_Prop.NNPP in LtA_ABC_DEF.

			exact LtA_ABC_DEF.
		}

		exact LtA_ABC_DEF.
	}
	exact LtA_ABC_DEF.
Qed.

End Euclid.
