Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_Euclid4.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_collinearright.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_oppositeside_onray_PABC_RQP_QABC.
Require Import ProofCheckingEuclid.lemma_right_triangle_NC.
Require Import ProofCheckingEuclid.lemma_right_triangle_leg_change.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_supp.
Require Import ProofCheckingEuclid.lemma_supplements_conga.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_11B.
Require Import ProofCheckingEuclid.proposition_12.
Require Import ProofCheckingEuclid.proposition_23.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_23B :
	forall A B C D E P,
	neq A B ->
	nCol D C E ->
	nCol A B P ->
	exists X Y, OnRay A B Y /\ CongA X A Y D C E /\ OppositeSide X A B P.
Proof.
	intros A B C D E P.
	intros neq_A_B.
	intros nCol_D_C_E.
	intros nCol_A_B_P.

	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (lemma_s_col_eq_A_C A B A eq_A_A) as Col_A_B_A.

	pose proof (lemma_NCdistinct _ _ _ nCol_D_C_E) as (neq_D_C & neq_C_E & neq_D_E & neq_C_D & neq_E_C & neq_E_D).
	pose proof (lemma_NCorder _ _ _ nCol_D_C_E) as (nCol_C_D_E & nCol_C_E_D & nCol_E_D_C & nCol_D_E_C & nCol_E_C_D).

	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_P) as (_ & neq_B_P & neq_A_P & neq_B_A & neq_P_B & neq_P_A).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_P) as (nCol_B_A_P & nCol_B_P_A & nCol_P_A_B & nCol_A_P_B & nCol_P_B_A).
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_P) as n_Col_A_B_P.

	pose proof (proposition_23 _ _ _ _ _ neq_A_B nCol_D_C_E) as (F & G & OnRay_AB_G & CongA_FAG_DCE).

	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_AB_G) as Col_A_B_G.
	pose proof (lemma_collinearorder _ _ _ Col_A_B_G) as (Col_B_A_G & Col_B_G_A & Col_G_A_B & Col_A_G_B & Col_G_B_A).

	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_FAG_DCE) as CongA_DCE_FAG.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_DCE_FAG) as nCol_F_A_G.
	pose proof (lemma_NCdistinct _ _ _ nCol_F_A_G) as (neq_F_A & neq_A_G & neq_F_G & neq_A_F & neq_G_A & neq_G_F).
	pose proof (lemma_NCorder _ _ _ nCol_F_A_G) as (nCol_A_F_G & nCol_A_G_F & nCol_G_F_A & nCol_F_G_A & nCol_G_A_F).
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_F_A_G) as n_Col_F_A_G.

	pose proof (lemma_s_onray_assert_ABB _ _ neq_A_F) as OnRay_AF_F.

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_G_F Col_A_G_B neq_A_B) as nCol_A_B_F.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_F) as n_Col_A_B_F.
	pose proof (lemma_NCorder _ _ _ nCol_A_B_F) as (nCol_B_A_F & nCol_B_F_A & nCol_F_A_B & nCol_A_F_B & nCol_F_B_A).


	pose proof (proposition_12 _ _ _ nCol_A_B_F) as (H & Perp_at_F_H_A_B_H).

	pose proof (cn_congruencereflexive H A) as Cong_HA_HA.

	destruct Perp_at_F_H_A_B_H as (J & _ & Col_A_B_H & Col_A_B_J & RightTriangle_JHF).

	pose proof (lemma_collinearorder _ _ _ Col_A_B_H) as (Col_B_A_H & Col_B_H_A & Col_H_A_B & Col_A_H_B & Col_H_B_A).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_J) as (Col_B_A_J & Col_B_J_A & Col_J_A_B & Col_A_J_B & Col_J_B_A).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_J Col_A_B_H neq_A_B) as Col_B_J_H.
	pose proof (lemma_collinearorder _ _ _ Col_B_J_H) as (Col_J_B_H & Col_J_H_B & Col_H_B_J & Col_B_H_J & Col_H_J_B).

	pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_A_B Col_A_B_J Col_A_B_H Col_A_B_G) as Col_J_H_G.

	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_JHF) as nCol_J_H_F.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_J_H_F) as n_Col_J_H_F.
	pose proof (lemma_NCdistinct _ _ _ nCol_J_H_F) as (neq_J_H & neq_H_F & neq_J_F & neq_H_J & neq_F_H & neq_F_J).
	pose proof (lemma_NCorder _ _ _ nCol_J_H_F) as (nCol_H_J_F & nCol_H_F_J & nCol_F_J_H & nCol_J_F_H & nCol_F_H_J).


	pose proof (lemma_extension _ _ _ _ neq_J_H neq_H_J) as (T & BetS_J_H_T & Cong_HT_HJ).

	pose proof (lemma_betweennotequal _ _ _ BetS_J_H_T) as (_ & _ & neq_J_T).
	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_J_H_T) as Col_J_H_T.
	pose proof (lemma_collinearorder _ _ _ Col_J_H_T) as (Col_H_J_T & Col_H_T_J & Col_T_J_H & Col_J_T_H & Col_T_H_J).


	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_J_B Col_H_J_T neq_H_J) as Col_J_B_T.
	pose proof (lemma_collinearorder _ _ _ Col_J_B_T) as (Col_B_J_T & Col_B_T_J & Col_T_J_B & Col_J_T_B & Col_T_B_J).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_J Col_B_A_H neq_B_A) as Col_A_J_H.
	pose proof (lemma_collinearorder _ _ _ Col_A_J_H) as (Col_J_A_H & Col_J_H_A & Col_H_A_J & Col_A_H_J & Col_H_J_A).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_J_A Col_H_J_T neq_H_J) as Col_J_A_T.
	pose proof (lemma_collinearorder _ _ _ Col_J_A_T) as (Col_A_J_T & Col_A_T_J & Col_T_J_A & Col_J_T_A & Col_T_A_J).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_J_T_A Col_J_T_B neq_J_T) as Col_T_A_B.
	pose proof (lemma_collinearorder _ _ _ Col_T_A_B) as (Col_A_T_B & Col_A_B_T & Col_B_T_A & Col_T_B_A & Col_B_A_T).

	assert (~ Col J T P) as n_Col_J_T_P.
	{
		intro Col_J_T_P.

		pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_J_T Col_J_T_A Col_J_T_B Col_J_T_P) as Col_A_B_P.

		contradict Col_A_B_P.
		exact n_Col_A_B_P.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_J_T_P) as nCol_J_T_P.
	pose proof (lemma_NCdistinct _ _ _ nCol_J_T_P) as (_ & neq_T_P & neq_J_P & neq_T_J & neq_P_T & neq_P_J).
	pose proof (lemma_NCorder _ _ _ nCol_J_T_P) as (nCol_T_J_P & nCol_T_P_J & nCol_P_J_T & nCol_J_P_T & nCol_P_T_J).


	pose proof (proposition_11B _ _ _ _ BetS_J_H_T nCol_J_T_P) as (Q & RightTriangle_JHQ & OppositeSide_Q_JT_P).
	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_JHQ) as nCol_J_H_Q.
	pose proof (lemma_NCdistinct _ _ _ nCol_J_H_Q) as (_ & neq_H_Q & neq_J_Q & _ & neq_Q_H & neq_Q_J).
	pose proof (lemma_NCorder _ _ _ nCol_J_H_Q) as (nCol_H_J_Q & nCol_H_Q_J & nCol_Q_J_H & nCol_J_Q_H & nCol_Q_H_J).

	pose proof (lemma_layoff _ _ _ _ neq_H_Q neq_H_F) as (S & OnRay_HQ_S & Cong_HS_HF).

	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_HQ_S) as OnRay_HS_Q.

	pose proof (lemma_doublereverse _ _ _ _ Cong_HS_HF) as (Cong_FH_SH & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_FH_SH) as (Cong_HF_HS & _ & _).

	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_JHQ OnRay_HQ_S) as RightTriangle_JHS.

	(* assert by cases *)
	assert (CongA F A G S A G) as CongA_FAG_SAG.
	assert (eq A H \/ neq A H) as [eq_A_H|neq_A_H] by (apply Classical_Prop.classic).
	{
		(* case eq_A_H *)
		assert (RightTriangle J A F) as RightTriangle_JAF by (rewrite eq_A_H; exact RightTriangle_JHF).
		assert (RightTriangle J A S) as RightTriangle_JAS by (rewrite eq_A_H; exact RightTriangle_JHS).
		assert (Col J A G) as Col_J_A_G by (rewrite eq_A_H; exact Col_J_H_G).

		pose proof (lemma_collinearright _ _ _ _ RightTriangle_JAF Col_J_A_G neq_G_A) as RightTriangle_GAF.
		pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_GAF) as RightTriangle_FAG.
		pose proof (lemma_collinearright _ _ _ _ RightTriangle_JAS Col_J_A_G neq_G_A) as RightTriangle_GAS.
		pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_GAS) as RightTriangle_SAG.
		pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_FAG RightTriangle_SAG) as CongA_FAG_SAG.

		exact CongA_FAG_SAG.
	}
	{
		(* case neq_A_H *)
		pose proof (lemma_inequalitysymmetric _ _ neq_A_H) as neq_H_A.

		pose proof (lemma_collinearright _ _ _ _ RightTriangle_JHF Col_J_H_A neq_A_H) as RightTriangle_AHF.
		pose proof (lemma_collinearright _ _ _ _ RightTriangle_JHS Col_J_H_A neq_A_H) as RightTriangle_AHS.
		pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_AHF) as RightTriangle_FHA.

		pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_FHA) as nCol_F_H_A.
		pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_AHS) as nCol_A_H_S.

		pose proof (lemma_NCorder _ _ _ nCol_F_H_A) as (nCol_H_F_A & nCol_H_A_F & nCol_A_F_H & nCol_F_A_H & nCol_A_H_F).

		pose proof (lemma_NCdistinct _ _ _ nCol_A_H_S) as (_ & neq_H_S & neq_A_S & _ & neq_S_H & neq_S_A).
		pose proof (lemma_NCorder _ _ _ nCol_A_H_S) as (nCol_H_A_S & nCol_H_S_A & nCol_S_A_H & nCol_A_S_H & nCol_S_H_A).

		pose proof (lemma_s_onray_assert_ABB _ _ neq_A_S) as OnRay_AS_S.

		pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_H_S) as CongA_AHS_SHA.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_F_A_H) as CongA_FAH_HAF.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_F_H_A) as CongA_FHA_AHF.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_H_A_S) as CongA_HAS_SAH.

		pose proof (lemma_equalanglesreflexive _ _ _ nCol_F_A_H) as CongA_FAH_FAH.
		pose proof (lemma_equalanglesreflexive _ _ _ nCol_S_A_H) as CongA_SAH_SAH.

		pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_AHF RightTriangle_AHS) as CongA_AHF_AHS.
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_FHA_AHF CongA_AHF_AHS) as CongA_FHA_AHS.
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_FHA_AHS CongA_AHS_SHA) as CongA_FHA_SHA.
		pose proof (proposition_04 _ _ _ _ _ _ Cong_HF_HS Cong_HA_HA CongA_FHA_SHA) as (_ & _ & CongA_HAF_HAS).
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_FAH_HAF CongA_HAF_HAS) as CongA_FAH_HAS.
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_FAH_HAS CongA_HAS_SAH) as CongA_FAH_SAH.

		(* assert by cases *)
		assert (Col G H A) as Col_G_H_A.
		assert (eq G H \/ neq G H) as [eq_G_H|neq_G_H] by (apply Classical_Prop.classic).
		{
			(* case eq_G_H *)
			pose proof (lemma_s_col_eq_A_B G H A eq_G_H) as Col_G_H_A.

			exact Col_G_H_A.
		}
		{
			(* case neq_G_H *)
			pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_A_B Col_A_B_G Col_A_B_H Col_A_B_A) as Col_G_H_A.

			exact Col_G_H_A.
		}

		(* assert by cases *)
		assert (CongA F A G S A G) as CongA_FAG_SAG.
		destruct Col_G_H_A as [eq_G_H | [eq_G_A | [eq_H_A | [BetS_H_G_A | [BetS_G_H_A | BetS_G_A_H]]]]].
		{
			(* case eq_G_H *)
			assert (CongA F A G S A G) as CongA_FAG_SAG by (rewrite eq_G_H; exact CongA_FAH_SAH).
			exact CongA_FAG_SAG.
		}
		{
			(* case eq_G_A *)

			contradict eq_G_A.
			exact neq_G_A.
		}
		{
			(* case eq_H_A *)
			contradict eq_H_A.
			exact neq_H_A.
		}
		{
			(* case BetS_H_G_A *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_G_A) as BetS_A_G_H.

			pose proof (lemma_s_onray_assert_bets_AEB _ _ _ BetS_A_G_H neq_A_H) as OnRay_AH_G.

			pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_FAH_FAH OnRay_AF_F OnRay_AH_G) as CongA_FAH_FAG.
			pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_SAH_SAH OnRay_AS_S OnRay_AH_G) as CongA_SAH_SAG.
			pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_FAH_FAG) as CongA_FAG_FAH.
			pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_FAG_FAH CongA_FAH_SAH) as CongA_FAG_SAH.
			pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_FAG_SAH CongA_SAH_SAG) as CongA_FAG_SAG.

			exact CongA_FAG_SAG.
		}
		{
			(* case BetS_G_H_A *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_H_A) as BetS_A_H_G.

			pose proof (lemma_s_onray_assert_bets_ABE _ _ _ BetS_A_H_G neq_A_H) as OnRay_AH_G.

			pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_FAH_FAH OnRay_AF_F OnRay_AH_G) as CongA_FAH_FAG.
			pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_SAH_SAH OnRay_AS_S OnRay_AH_G) as CongA_SAH_SAG.
			pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_FAH_FAG) as CongA_FAG_FAH.
			pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_FAG_FAH CongA_FAH_SAH) as CongA_FAG_SAH.
			pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_FAG_SAH CongA_SAH_SAG) as CongA_FAG_SAG.

			exact CongA_FAG_SAG.
		}
		{
			(* case BetS_G_A_H *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_A_H) as BetS_H_A_G.
			pose proof (lemma_s_supp _ _ _ _ _ OnRay_AF_F BetS_H_A_G) as Supp_HAF_FAG.
			pose proof (lemma_s_supp _ _ _ _ _ OnRay_AS_S BetS_H_A_G) as Supp_HAS_SAG.
			pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_HAF_HAS Supp_HAF_FAG Supp_HAS_SAG) as CongA_FAG_SAG.

			exact CongA_FAG_SAG.
		}

		exact CongA_FAG_SAG.
	}

	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_FAG_SAG) as CongA_SAG_FAG.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_SAG_FAG CongA_FAG_DCE) as CongA_SAG_DCE.

	pose proof (lemma_oppositeside_onray_PABC_RQP_QABC _ _ _ _ _ _ OppositeSide_Q_JT_P OnRay_HS_Q Col_J_T_H) as OppositeSide_S_JT_P.

	destruct OppositeSide_S_JT_P as (M & BetS_S_M_P & Col_J_T_M & nCol_J_T_S).

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_J_T_S) as n_Col_J_T_S.

	assert (~ Col A B S) as n_Col_A_B_S.
	{
		intro Col_A_B_S.

		pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_A_B Col_A_B_J Col_A_B_T Col_A_B_S) as Col_J_T_S.

		contradict Col_J_T_S.
		exact n_Col_J_T_S.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_B_S) as nCol_A_B_S.

	pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_J_T Col_J_T_A Col_J_T_B Col_J_T_M) as Col_A_B_M.

	pose proof (lemma_s_os _ _ _ _ _ BetS_S_M_P Col_A_B_M nCol_A_B_S) as OppositeSide_S_AB_P.


	exists S, G.
	split.
	exact OnRay_AB_G.
	split.
	exact CongA_SAG_DCE.
	exact OppositeSide_S_AB_P.
Qed.

End Euclid.
