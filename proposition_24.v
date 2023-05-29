Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence_smaller.
Require Import ProofCheckingEuclid.lemma_angleordertransitive.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_crossbar.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalanglesflip.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_lessthancongruence_smaller.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_neq_A_B.
Require Import ProofCheckingEuclid.lemma_onray_orderofpoints_any.
Require Import ProofCheckingEuclid.lemma_onray_shared_initial_point.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_lt.
Require Import ProofCheckingEuclid.lemma_s_lta.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_05.
Require Import ProofCheckingEuclid.proposition_16.
Require Import ProofCheckingEuclid.proposition_19.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_24 :
	forall A B C D E F,
	Triangle A B C ->
	Triangle D E F ->
	Cong A B D E ->
	Cong A C D F ->
	LtA E D F B A C ->
	Lt E F B C.
Proof.
	intros A B C D E F.
	intros Triangle_A_B_C.
	intros Triangle_D_E_F.
	intros Cong_A_B_D_E.
	intros Cong_A_C_D_F.
	intros LtA_E_D_F_B_A_C.

	pose proof (lemma_s_ncol_triangle _ _ _ Triangle_A_B_C) as nCol_A_B_C.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).

	
	destruct LtA_E_D_F_B_A_C as (P & T & Q & BetS_P_T_Q & OnRay_A_B_P & OnRay_A_C_Q & CongA_E_D_F_B_A_T).
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_E_D_F_B_A_T) as nCol_B_A_T.

	pose proof (lemma_NCdistinct _ _ _ nCol_B_A_T) as (_ & neq_A_T & neq_B_T & _ & neq_T_A & neq_T_B).
	pose proof (lemma_NCorder _ _ _ nCol_B_A_T) as (nCol_A_B_T & nCol_A_T_B & nCol_T_B_A & nCol_B_T_A & nCol_T_A_B).

	pose proof (lemma_layoff _ _ _ _ neq_A_T neq_A_C (* not real *)) as (H & OnRay_A_T_H & Cong_A_H_A_C).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_A_H_A_C Cong_A_C_D_F) as Cong_A_H_D_F.

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_B_A_T) as n_Col_B_A_T.

	assert (~ Col H A B) as n_Col_H_A_B.
	{
		intro Col_H_A_B.

		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_A_T_H) as Col_A_T_H.
		pose proof (lemma_collinearorder _ _ _ Col_A_T_H) as (_ & _ & Col_H_A_T & _ & _).
		pose proof (lemma_onray_strict _ _ _ OnRay_A_T_H) as neq_A_H.
		pose proof (lemma_inequalitysymmetric _ _ neq_A_H) as neq_H_A.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_A_B Col_H_A_T neq_H_A) as Col_A_B_T.
		pose proof (lemma_collinearorder _ _ _ Col_A_B_T) as (Col_B_A_T & _ & _ & _ & _).

		contradict Col_B_A_T.
		exact n_Col_B_A_T.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_H_A_B) as nCol_H_A_B.
	pose proof (lemma_NCdistinct _ _ _ nCol_H_A_B) as (neq_H_A & _ & neq_H_B & neq_A_H & _ & neq_B_H).
	pose proof (lemma_NCorder _ _ _ nCol_H_A_B) as (nCol_A_H_B & nCol_A_B_H & nCol_B_H_A & nCol_H_B_A & nCol_B_A_H).

	assert (eq B B) as eq_B_B by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB A B neq_A_B) as OnRay_A_B_B.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_E_D_F_B_A_T OnRay_A_B_B OnRay_A_T_H) as CongA_E_D_F_B_A_H.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_E_D_F_B_A_H) as CongA_B_A_H_E_D_F.
	pose proof (lemma_equalanglesflip _ _ _ _ _ _ CongA_B_A_H_E_D_F) as CongA_H_A_B_F_D_E.

	epose proof (proposition_04 A H B D F E Cong_A_H_D_F Cong_A_B_D_E CongA_H_A_B_F_D_E) as (Cong_H_B_F_E & CongA_A_H_B_D_F_E & CongA_A_B_H_D_E_F).

	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_A_C_Q) as OnRay_A_Q_C.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_A_B_P) as OnRay_A_P_B.
	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_A_Q_C) as Col_A_Q_C.
	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_A_P_B) as Col_A_P_B.

	assert (~ Col Q A P) as n_Col_Q_A_P.
	{
		intro Col_Q_A_P.
		pose proof (lemma_collinearorder _ _ _ Col_Q_A_P) as (_ & Col_A_P_Q & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_A_Q_C) as (Col_Q_A_C & _ & _ & _ & _).
		pose proof (lemma_onray_neq_A_B _ _ _ OnRay_A_Q_C) as neq_A_Q.
		pose proof (lemma_inequalitysymmetric _ _ neq_A_Q) as neq_Q_A.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_A_C Col_Q_A_P neq_Q_A) as Col_A_C_P.
		pose proof (lemma_collinearorder _ _ _ Col_A_P_B) as (Col_P_A_B & _ & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_A_C_P) as (_ & _ & Col_P_A_C & _ & _).
		pose proof (lemma_onray_strict _ _ _ OnRay_A_B_P) as neq_A_P.
		pose proof (lemma_inequalitysymmetric _ _ neq_A_P) as neq_P_A.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_P_A_B Col_P_A_C neq_P_A) as Col_A_B_C.

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_Q_A_P) as nCol_Q_A_P.

	pose proof (lemma_s_triangle _ _ _ nCol_Q_A_P) as Triangle_Q_A_P.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_T_Q) as BetS_Q_T_P.
	epose proof (lemma_crossbar _ A _ T C B Triangle_Q_A_P BetS_Q_T_P OnRay_A_Q_C OnRay_A_P_B) as (J & OnRay_A_T_J & BetS_C_J_B).
	pose proof (lemma_onray_shared_initial_point _ _ _ _ OnRay_A_T_J OnRay_A_T_H) as OnRay_A_J_H.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_A_H_A_C) as Cong_A_C_A_H.

	assert (~ Col A C H) as n_Col_A_C_H.
	{
		intro Col_A_C_H.
		pose proof (lemma_collinearorder _ _ _ Col_A_C_H) as (_ & _ & Col_H_A_C & _ & _).
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_A_J_H) as Col_A_J_H.
		pose proof (lemma_collinearorder _ _ _ Col_A_J_H) as (_ & _ & Col_H_A_J & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_A_C Col_H_A_J neq_H_A) as Col_A_C_J.
		pose proof (lemma_s_col_BetS_A_B_C C J B BetS_C_J_B) as Col_C_J_B.
		pose proof (lemma_collinearorder _ _ _ Col_A_C_J) as (_ & Col_C_J_A & _ & _ & _).
		pose proof (lemma_betweennotequal _ _ _ BetS_C_J_B) as (_ & neq_C_J & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_J_B Col_C_J_A neq_C_J) as Col_J_B_A.
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_A_T_J) as Col_A_T_J.
		pose proof (lemma_collinearorder _ _ _ Col_A_T_J) as (_ & _ & Col_J_A_T & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_J_B_A) as (_ & _ & _ & Col_J_A_B & _).
		pose proof (lemma_onray_strict _ _ _ OnRay_A_T_J) as neq_A_J.
		pose proof (lemma_inequalitysymmetric _ _ neq_A_J) as neq_J_A.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_J_A_T Col_J_A_B neq_J_A) as Col_A_T_B.
		pose proof (lemma_collinearorder _ _ _ Col_A_T_B) as (_ & _ & Col_B_A_T & _ & _).

		contradict Col_B_A_T.
		exact n_Col_B_A_T.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_C_H) as nCol_A_C_H.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_C_H) as (_ & neq_C_H & _ & _ & neq_H_C & _).
	pose proof (lemma_NCorder _ _ _ nCol_A_C_H) as (nCol_C_A_H & nCol_C_H_A & nCol_H_A_C & nCol_A_H_C & nCol_H_C_A).

	pose proof (lemma_s_triangle _ _ _ nCol_A_C_H) as Triangle_A_C_H.
	epose proof (lemma_s_isosceles _ _ _ Triangle_A_C_H Cong_A_C_A_H) as isosceles_A_C_H.
	pose proof (proposition_05 _ _ _ isosceles_A_C_H) as CongA_A_C_H_A_H_C.

	(* assert by cases *)
	assert (Lt H B C B) as Lt_H_B_C_B.
	pose proof (lemma_onray_orderofpoints_any _ _ _ OnRay_A_J_H) as [BetS_A_H_J | [eq_J_H | BetS_A_J_H]].
	{
		(* case BetS_A_H_J *)

		assert (~ Col C J H) as n_Col_C_J_H.
		{
			intro Col_C_J_H.
			pose proof (lemma_s_col_BetS_A_B_C A H J BetS_A_H_J) as Col_A_H_J.
			pose proof (lemma_collinearorder _ _ _ Col_A_H_J) as (_ & _ & _ & _ & Col_J_H_A).
			pose proof (lemma_collinearorder _ _ _ Col_C_J_H) as (_ & Col_J_H_C & _ & _ & _).
			pose proof (lemma_betweennotequal _ _ _ BetS_A_H_J) as (neq_H_J & _ & _).
			pose proof (lemma_inequalitysymmetric _ _ neq_H_J) as neq_J_H.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_J_H_A Col_J_H_C neq_J_H) as Col_H_A_C.
			pose proof (lemma_collinearorder _ _ _ Col_H_A_C) as (_ & Col_A_C_H & _ & _ & _).

			contradict Col_A_C_H.
			exact n_Col_A_C_H.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_C_J_H) as nCol_C_J_H.
		pose proof (lemma_NCdistinct _ _ _ nCol_C_J_H) as (neq_C_J & neq_J_H & _ & neq_J_C & neq_H_J & _).
		pose proof (lemma_NCorder _ _ _ nCol_C_J_H) as (nCol_J_C_H & nCol_J_H_C & nCol_H_C_J & nCol_C_H_J & nCol_H_J_C).
		pose proof (lemma_s_ncol_n_col _ _ _ nCol_C_H_J) as n_Col_C_H_J.

		pose proof (lemma_s_triangle _ _ _ nCol_C_J_H) as Triangle_C_J_H.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_H_J) as BetS_J_H_A.

		pose proof (proposition_16 _ _ _ _ Triangle_C_J_H BetS_J_H_A) as (LtA_J_C_H_C_H_A & _).

		pose proof (lemma_ABCequalsCBA _ _ _ nCol_H_C_J) as CongA_H_C_J_J_C_H.
		pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_J_C_H_C_H_A CongA_H_C_J_J_C_H) as LtA_H_C_J_C_H_A.


		pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_H_C) as CongA_A_H_C_C_H_A.
		pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_H_C_J_C_H_A CongA_A_H_C_C_H_A) as LtA_H_C_J_A_H_C.
		pose proof (lemma_s_onray_assert_ABB H B neq_H_B) as OnRay_H_B_B.
		assert (eq C C) as eq_C_C by (reflexivity).


		pose proof (lemma_s_onray_assert_ABB H C neq_H_C) as OnRay_H_C_C.
		pose proof (lemma_equalanglesreflexive _ _ _ nCol_C_H_J) as CongA_C_H_J_C_H_J.
		epose proof (lemma_s_lta C H J C H B C J B BetS_C_J_B OnRay_H_C_C OnRay_H_B_B CongA_C_H_J_C_H_J) as LtA_C_H_J_C_H_B. (* conclude_def *)



		pose proof (lemma_s_triangle _ _ _ nCol_C_A_H) as Triangle_C_A_H.

		pose proof (proposition_16 _ _ _ _ Triangle_C_A_H BetS_A_H_J) as (LtA_A_C_H_C_H_J & _).
		pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_H_C_J_A_H_C CongA_A_C_H_A_H_C) as LtA_H_C_J_A_C_H.
		pose proof (lemma_angleordertransitive _ _ _ _ _ _ _ _ _ LtA_H_C_J_A_C_H LtA_A_C_H_C_H_J) as LtA_H_C_J_C_H_J.
		pose proof (lemma_angleordertransitive _ _ _ _ _ _ _ _ _ LtA_H_C_J_C_H_J LtA_C_H_J_C_H_B) as LtA_H_C_J_C_H_B.
		assert (eq H H) as eq_H_H by (reflexivity).
		pose proof (lemma_s_onray_assert_ABB C H neq_C_H) as OnRay_C_H_H.
		pose proof (lemma_s_onray_assert_bets_ABE C J B BetS_C_J_B neq_C_J) as OnRay_C_J_B.
		pose proof (lemma_equalanglesreflexive _ _ _ nCol_H_C_J) as CongA_H_C_J_H_C_J.
		pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_H_C_J_H_C_J OnRay_C_H_H OnRay_C_J_B) as CongA_H_C_J_H_C_B.
		pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_H_C_J_H_C_B) as CongA_H_C_B_H_C_J.
		pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_H_C_J_C_H_B CongA_H_C_B_H_C_J) as LtA_H_C_B_C_H_B.

		assert (~ Col B H C) as n_Col_B_H_C.
		{
			intro Col_B_H_C.
			pose proof (lemma_s_col_BetS_A_B_C C J B BetS_C_J_B) as Col_C_J_B.
			pose proof (lemma_collinearorder _ _ _ Col_B_H_C) as (_ & _ & _ & Col_B_C_H & _).
			pose proof (lemma_collinearorder _ _ _ Col_C_J_B) as (_ & _ & Col_B_C_J & _ & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_C_H Col_B_C_J neq_B_C) as Col_C_H_J.
			contradict Col_C_H_J.
			exact n_Col_C_H_J.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_B_H_C) as nCol_B_H_C.

		pose proof (lemma_s_triangle _ _ _ nCol_B_H_C) as Triangle_B_H_C.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_H_C) as CongA_B_H_C_C_H_B.
		pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_H_C_B_C_H_B CongA_B_H_C_C_H_B) as LtA_H_C_B_B_H_C.
		pose proof (proposition_19 _ _ _ Triangle_B_H_C LtA_H_C_B_B_H_C) as Lt_B_H_B_C.
		pose proof (cn_congruencereverse B H) as Cong_B_H_H_B.
		pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_B_H_B_C Cong_B_H_H_B) as Lt_H_B_B_C.
		pose proof (cn_congruencereverse B C) as Cong_B_C_C_B.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_H_B_B_C Cong_B_C_C_B) as Lt_H_B_C_B.

		exact Lt_H_B_C_B.
	}
	{
		(* case eq_J_H *)
		
		assert (BetS C H B) as BetS_C_H_B by (rewrite <- eq_J_H; exact BetS_C_J_B).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_H_B) as BetS_B_H_C.
		pose proof (cn_congruencereverse B H) as Cong_B_H_H_B.
		pose proof (lemma_s_lt _ _ _ _ _ BetS_B_H_C Cong_B_H_H_B) as Lt_H_B_B_C.
		pose proof (cn_congruencereverse B C) as Cong_B_C_C_B.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_H_B_B_C Cong_B_C_C_B) as Lt_H_B_C_B.

		exact Lt_H_B_C_B.
	}
	{
		(* case BetS_A_J_H *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_J_H) as BetS_H_J_A.

		assert (~ Col C J H) as n_Col_C_J_H.
		{
			intro Col_C_J_H.
			pose proof (lemma_s_col_BetS_A_C_B A H J BetS_A_J_H) as Col_A_H_J.
			pose proof (lemma_collinearorder _ _ _ Col_A_H_J) as (_ & _ & _ & _ & Col_J_H_A).
			pose proof (lemma_collinearorder _ _ _ Col_C_J_H) as (_ & Col_J_H_C & _ & _ & _).
			pose proof (lemma_betweennotequal _ _ _ BetS_A_J_H) as (neq_J_H & _ & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_J_H_A Col_J_H_C neq_J_H) as Col_H_A_C.
			pose proof (lemma_collinearorder _ _ _ Col_H_A_C) as (_ & Col_A_C_H & _ & _ & _).
			contradict Col_A_C_H.
			exact n_Col_A_C_H.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_C_J_H) as nCol_C_J_H.

		assert (~ Col H C B) as n_Col_H_C_B.
		{
			intro Col_H_C_B.
			pose proof (lemma_s_col_BetS_A_B_C C J B BetS_C_J_B) as Col_C_J_B.
			pose proof (lemma_collinearorder _ _ _ Col_C_J_B) as (_ & _ & Col_B_C_J & _ & _).
			pose proof (lemma_collinearorder _ _ _ Col_H_C_B) as (_ & _ & _ & _ & Col_B_C_H).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_C_H Col_B_C_J neq_B_C) as Col_C_H_J.
			pose proof (lemma_collinearorder _ _ _ Col_C_H_J) as (_ & _ & _ & Col_C_J_H & _).
			contradict Col_C_J_H.
			exact n_Col_C_J_H.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_H_C_B) as nCol_H_C_B.
		pose proof (lemma_NCorder _ _ _ nCol_H_C_B) as (nCol_C_H_B & nCol_C_B_H & nCol_B_H_C & nCol_H_B_C & nCol_B_C_H).

		assert (eq H H) as eq_H_H by (reflexivity).
		assert (eq A A) as eq_A_A by (reflexivity).

		pose proof (lemma_s_onray_assert_ABB C A neq_C_A) as OnRay_C_A_A.
		pose proof (lemma_equalanglesreflexive _ _ _ nCol_H_C_B) as CongA_H_C_B_H_C_B.
pose proof (lemma_s_onray_assert_bets_AEB C B J BetS_C_J_B neq_C_B) as OnRay_C_B_J.
		pose proof (lemma_s_onray_assert_ABB C H neq_C_H) as OnRay_C_H_H.
		pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_H_C_B_H_C_B OnRay_C_H_H OnRay_C_B_J) as CongA_H_C_B_H_C_J.

		epose proof (lemma_s_lta H C B H C A H J A BetS_H_J_A OnRay_C_H_H OnRay_C_A_A CongA_H_C_B_H_C_J) as LtA_H_C_B_H_C_A. (* conclude_def *)

		pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_C_H) as CongA_B_C_H_H_C_B.
		pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_H_C_B_H_C_A CongA_B_C_H_H_C_B) as LtA_B_C_H_H_C_A.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_C_H) as CongA_A_C_H_H_C_A.
		pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_B_C_H_H_C_A CongA_A_C_H_H_C_A) as LtA_B_C_H_A_C_H.
		pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_C_H_A_H_C) as CongA_A_H_C_A_C_H.
		pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_B_C_H_A_C_H CongA_A_H_C_A_C_H) as LtA_B_C_H_A_H_C.


		pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_H_C) as CongA_A_H_C_C_H_A.
		assert (eq C C) as eq_C_C by (reflexivity).
		pose proof (lemma_s_onray_assert_ABB H C neq_H_C) as OnRay_H_C_C.
		pose proof (lemma_s_onray_assert_ABB H B neq_H_B) as OnRay_H_B_B.
pose proof (lemma_s_onray_assert_bets_AEB H A J BetS_H_J_A neq_H_A) as OnRay_H_A_J.
		pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_A_H_C_C_H_A OnRay_H_C_C OnRay_H_A_J) as CongA_A_H_C_C_H_J.

		epose proof (lemma_s_lta A H C C H B C J B BetS_C_J_B OnRay_H_C_C OnRay_H_B_B CongA_A_H_C_C_H_J) as LtA_A_H_C_C_H_B. (* conclude_def *)


		pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_H_C) as CongA_B_H_C_C_H_B.
		pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_A_H_C_C_H_B CongA_B_H_C_C_H_B) as LtA_A_H_C_B_H_C.
		pose proof (lemma_angleordertransitive _ _ _ _ _ _ _ _ _ LtA_B_C_H_A_H_C LtA_A_H_C_B_H_C) as LtA_B_C_H_B_H_C.


		pose proof (lemma_ABCequalsCBA _ _ _ nCol_H_C_B) as CongA_H_C_B_B_C_H.
		pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_B_C_H_B_H_C CongA_H_C_B_B_C_H) as LtA_H_C_B_B_H_C.
		pose proof (lemma_s_triangle _ _ _ nCol_B_H_C) as Triangle_B_H_C.
		pose proof (proposition_19 _ _ _ Triangle_B_H_C LtA_H_C_B_B_H_C) as Lt_B_H_B_C.
		pose proof (cn_congruencereverse B H) as Cong_B_H_H_B.
		pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_B_H_B_C Cong_B_H_H_B) as Lt_H_B_B_C.
		pose proof (cn_congruencereverse B C) as Cong_B_C_C_B.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_H_B_B_C Cong_B_C_C_B) as Lt_H_B_C_B.

		exact Lt_H_B_C_B.
	}
	pose proof (cn_congruencereverse F E) as Cong_F_E_E_F.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_H_B_F_E Cong_F_E_E_F) as Cong_H_B_E_F.
	pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_H_B_C_B Cong_H_B_E_F) as Lt_E_F_C_B.
	pose proof (cn_congruencereverse C B) as Cong_C_B_B_C.
	pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_E_F_C_B Cong_C_B_B_C) as Lt_E_F_B_C.

	exact Lt_E_F_B_C.
Qed.

End Euclid.
