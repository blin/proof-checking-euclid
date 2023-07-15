Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angleordertransitive.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_shared_initial_point.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_SameSide.
Require Import ProofCheckingEuclid.lemma_sameside_onray.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.
Require Import ProofCheckingEuclid.proposition_07.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_angletrichotomy :
	forall A B C D E F,
	LtA A B C D E F ->
	~ LtA D E F A B C.
Proof.
	intros A B C D E F.
	intros LtA_ABC_DEF.

	assert (~ LtA D E F A B C) as n_LtA_DEF_ABC.
	{
		intros LtA_DEF_ABC.

		pose proof (lemma_angleordertransitive _ _ _ _ _ _ _ _ _ LtA_ABC_DEF LtA_DEF_ABC) as LtA_ABC_ABC.

		destruct LtA_ABC_ABC as (G & H & J & BetS_G_H_J & OnRay_BA_G & OnRay_BC_J & CongA_ABC_ABH).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_H_J) as BetS_J_H_G.
		pose proof (lemma_betweennotequal _ _ _ BetS_G_H_J) as (_ & neq_G_H & _).
		pose proof (lemma_betweennotequal _ _ _ BetS_J_H_G) as (_ & neq_J_H & _).
		pose proof (lemma_inequalitysymmetric _ _ neq_G_H) as neq_H_G.
		pose proof (lemma_inequalitysymmetric _ _ neq_J_H) as neq_H_J.

		assert (Col G H J) as Col_G_H_J by (unfold Col; one_of_disjunct BetS_G_H_J).
		pose proof (lemma_collinearorder _ _ _ Col_G_H_J) as (_ & Col_H_J_G & _ & _ & _).

		pose proof (lemma_onray_strict _ _ _ OnRay_BA_G) as neq_B_G.
		pose proof (lemma_inequalitysymmetric _ _ neq_B_G) as neq_G_B.
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_BA_G) as Col_B_A_G.
		pose proof (lemma_collinearorder _ _ _ Col_B_A_G) as (Col_A_B_G & _ & Col_G_B_A  & Col_B_G_A  & _).

		pose proof (lemma_onray_strict _ _ _ OnRay_BC_J) as neq_B_J.
		pose proof (lemma_inequalitysymmetric _ _ neq_B_J) as neq_J_B.
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_BC_J) as Col_B_C_J.
		pose proof (lemma_collinearorder _ _ _ Col_B_C_J) as (_ & _ & Col_J_B_C & Col_B_J_C  & _).

		destruct CongA_ABC_ABH as (U & V & u & v & OnRay_BA_U & OnRay_BC_V & OnRay_BA_u & OnRay_BH_v & Cong_BU_Bu & Cong_BV_Bv & Cong_UV_uv & nCol_A_B_C).

		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_BA_U) as Col_B_A_U.
		pose proof (lemma_collinearorder _ _ _ Col_B_A_U) as (_ & _ & Col_U_B_A & _ & _).
		pose proof (lemma_onray_strict _ _ _ OnRay_BA_U) as neq_B_U.
		pose proof (lemma_inequalitysymmetric _ _ neq_B_U) as neq_U_B.
		pose proof (lemma_onray_shared_initial_point _ _ _ _ OnRay_BA_G OnRay_BA_U) as OnRay_BG_U.
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_BG_U) as Col_B_G_U.
		pose proof (lemma_collinearorder _ _ _ Col_B_G_U) as (_ & _ & _ & Col_B_U_G & _).

		pose proof (lemma_layoffunique _ _ _ _ OnRay_BA_U OnRay_BA_u Cong_BU_Bu) as eq_U_u.
		assert (Cong U V U v) as Cong_UV_Uv by (rewrite eq_U_u at 2; exact Cong_UV_uv).
		pose proof (lemma_congruenceflip _ _ _ _ Cong_UV_Uv) as (Cong_VU_vU & _ & _).

		pose proof (lemma_onray_shared_initial_point _ _ _ _ OnRay_BC_J OnRay_BC_V) as OnRay_BJ_V.
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_BJ_V) as Col_B_J_V.
		pose proof (lemma_collinearorder _ _ _ Col_B_J_V) as (_ & _ & Col_V_B_J & _ & _).

		pose proof (lemma_congruenceflip _ _ _ _ Cong_BV_Bv) as (Cong_VB_vB & _ & _).

		pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.
		pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & _ & _ & _ & _ & _).
		pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & _ & _ & _).

		pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_C_A Col_B_C_J neq_B_J) as nCol_B_J_A.
		pose proof (lemma_NCorder _ _ _ nCol_B_J_A) as (_ & _ & _ & nCol_B_A_J & _).
		pose proof (lemma_s_ncol_n_col _ _ _ nCol_B_A_J) as n_Col_B_A_J.

		pose proof (postulate_Euclid2 _ _ neq_H_G) as (P & BetS_H_G_P).

		pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_J_H_G BetS_H_G_P) as BetS_J_G_P.

		pose proof (by_def_OppositeSide _ _ _ _ _ BetS_J_G_P Col_B_A_G nCol_B_A_J) as OppositeSide_J_BA_P.


		assert (~ Col B U H) as n_Col_B_U_H.
		{
			intros Col_B_U_H.

			pose proof (lemma_collinearorder _ _ _ Col_B_U_H) as (Col_U_B_H & _ & _ & _ & _).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_U_B_A Col_U_B_H neq_U_B) as Col_B_A_H.
			pose proof (lemma_collinearorder _ _ _ Col_B_A_H) as (Col_A_B_H & _ & Col_H_B_A & _ & _).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_G Col_A_B_H neq_A_B) as Col_B_G_H.
			pose proof (lemma_collinearorder _ _ _ Col_B_G_H) as (_ & Col_G_H_B & _ & _ & _).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_H_B Col_G_H_J neq_G_H) as Col_H_B_J.

			assert (~ neq H B) as eq_H_B.
			{
				intros neq_H_B.

				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_B_J Col_H_B_A neq_H_B) as Col_B_J_A.
				pose proof (lemma_collinearorder _ _ _ Col_B_J_A) as (_ & _ & _ & Col_B_A_J & _).

				contradict Col_B_A_J.
				exact n_Col_B_A_J.
			}
			apply Classical_Prop.NNPP in eq_H_B.

			assert (BetS G B J) as BetS_G_B_J by (rewrite <- eq_H_B; exact BetS_G_H_J).
			pose proof (lemma_betweennotequal _ _ _ BetS_G_B_J) as (_ & _ & neq_G_J).

			assert (Col G B J) as Col_G_B_J by (unfold Col; one_of_disjunct BetS_G_B_J).
			pose proof (lemma_collinearorder _ _ _ Col_G_B_J) as (Col_B_G_J & _ & _ & Col_G_J_B & _).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_G_J Col_B_G_A neq_B_G) as Col_G_J_A.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_J_A Col_G_J_B neq_G_J) as Col_J_A_B.
			pose proof (lemma_collinearorder _ _ _ Col_J_A_B) as (_ & _ & _ & _ & Col_B_A_J).

			contradict Col_B_A_J.
			exact n_Col_B_A_J.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_B_U_H) as nCol_B_U_H.

		pose proof (by_def_OppositeSide _ _ _ _ _ BetS_H_G_P Col_B_U_G nCol_B_U_H) as OppositeSide_H_BU_P.

		pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_A_C Col_B_A_U neq_B_U) as nCol_B_U_C.
		pose proof (lemma_NCorder _ _ _ nCol_B_U_C) as (_ & _ & _ & nCol_B_C_U & _).
		pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_C_U Col_B_C_J neq_B_J) as nCol_B_J_U.
		pose proof (lemma_NCorder _ _ _ nCol_B_J_U) as (_ & _ & _ & nCol_B_U_J & _).

		pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_B_U_G Col_B_U_G BetS_J_G_P BetS_H_G_P nCol_B_U_J nCol_B_U_H) as SameSide_J_H_BU.
		pose proof (lemma_samesidesymmetric _ _ _ _ SameSide_J_H_BU) as (SameSide_H_J_BU & _ & _).
		assert (eq B B) as eq_B_B by (reflexivity).
		assert (Col B B U) as Col_B_B_U by (unfold Col; one_of_disjunct eq_B_B).
		pose proof (lemma_sameside_onray _ _ _ _ _ _ SameSide_H_J_BU Col_B_B_U OnRay_BJ_V) as SameSide_H_V_BU.
		pose proof (lemma_samesidesymmetric _ _ _ _ SameSide_H_V_BU) as (SameSide_V_H_BU & _ & _).
		pose proof (lemma_sameside_onray _ _ _ _ _ _ SameSide_V_H_BU Col_B_B_U OnRay_BH_v) as SameSide_V_v_BU.

		pose proof (proposition_07 _ _ _ _ neq_B_U Cong_VB_vB Cong_VU_vU SameSide_V_v_BU) as eq_V_v.
		assert (OnRay B H V) as OnRay_BH_V by (rewrite eq_V_v; exact OnRay_BH_v).
		pose proof (lemma_onray_strict _ _ _ OnRay_BH_V) as neq_B_V.
		pose proof (lemma_inequalitysymmetric _ _ neq_B_V) as neq_V_B.
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_BH_V) as Col_B_H_V.
		pose proof (lemma_collinearorder _ _ _ Col_B_H_V) as (_ & _ & Col_V_B_H & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_V_B_J Col_V_B_H neq_V_B) as Col_B_J_H.
		pose proof (lemma_collinearorder _ _ _ Col_B_J_H) as (_ & _ & _ & _ & Col_H_J_B).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_J_B Col_H_J_G neq_H_J) as Col_J_B_G.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_J_B_G Col_J_B_C neq_J_B) as Col_B_G_C.
		pose proof (lemma_collinearorder _ _ _ Col_B_G_C) as (Col_G_B_C & _ & _ & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_B_C Col_G_B_A neq_G_B) as Col_B_C_A.
		pose proof (lemma_collinearorder _ _ _ Col_B_C_A) as (_ & _ & Col_A_B_C & _ & _).

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	exact n_LtA_DEF_ABC.
Qed.

End Euclid.
