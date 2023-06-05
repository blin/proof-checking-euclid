Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence_smaller.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_oppositesidesymmetric.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_outerconnectivity.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_conga.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_lta.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_ss.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_sameside2.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.
Require Import ProofCheckingEuclid.proposition_23C.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_angletrichotomy_asymmetric :
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
	intros n_CongA_A_B_C_D_E_F.
	intros n_LtA_D_E_F_A_B_C.

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.

	assert (~ eq B A) as n_eq_B_A.
	{
		intro eq_B_A.
		pose proof (lemma_equalitysymmetric _ _ eq_B_A) as eq_A_B.
		pose proof (lemma_s_col_eq_A_B A B C eq_A_B) as Col_A_B_C.
		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	assert (neq_B_A := n_eq_B_A).



	assert (~ eq B C) as n_eq_B_C.
	{
		intro eq_B_C.
		pose proof (lemma_s_col_eq_B_C A B C eq_B_C) as Col_A_B_C.
		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	assert (neq_B_C := n_eq_B_C).



	assert (~ Col B A C) as n_Col_B_A_C.
	{
		intro Col_B_A_C.
		pose proof (lemma_collinearorder _ _ _ Col_B_A_C) as (Col_A_B_C & _ & _ & _ & _).
		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_B_A_C) as nCol_B_A_C.

	pose proof (proposition_23C _ _ _ _ _ _ neq_B_A nCol_D_E_F nCol_B_A_C) as (G & J & OnRay_B_A_J & CongA_G_B_J_D_E_F & SS_G_C_B_A).

	assert (SS_G_C_B_A2 := SS_G_C_B_A).
	destruct SS_G_C_B_A2 as (_ & _ & _ & _ & _ & _ & _ & nCol_B_A_G & _).
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_B_A_G) as n_Col_B_A_G.

	assert (~ eq B G) as n_eq_B_G.
	{
		intro eq_B_G.
		pose proof (lemma_s_col_eq_A_C B A G eq_B_G) as Col_B_A_G.
		contradict Col_B_A_G.
		exact n_Col_B_A_G.
	}
	assert (neq_B_G := n_eq_B_G).



	assert (~ eq A G) as n_eq_A_G.
	{
		intro eq_A_G.
		pose proof (lemma_s_col_eq_B_C B A G eq_A_G) as Col_B_A_G.
		contradict Col_B_A_G.
		exact n_Col_B_A_G.
	}
	assert (neq_A_G := n_eq_A_G).


	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_G_B_J_D_E_F) as CongA_D_E_F_G_B_J.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_B_A_J) as OnRay_B_J_A.
	assert (eq G G) as eq_G_G by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB B G neq_B_G) as OnRay_B_G_G.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_D_E_F_G_B_J OnRay_B_G_G OnRay_B_J_A) as CongA_D_E_F_G_B_A.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_D_E_F_G_B_A) as nCol_G_B_A.

	assert (~ Col A B G) as n_Col_A_B_G.
	{
		intro Col_A_B_G.
		pose proof (lemma_collinearorder _ _ _ Col_A_B_G) as (Col_B_A_G & _ & _ & _ & _).
		contradict Col_B_A_G.
		exact n_Col_B_A_G.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_B_G) as nCol_A_B_G.

	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_D_E_F_G_B_A) as CongA_G_B_A_D_E_F.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_B_G) as CongA_A_B_G_G_B_A.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_B_G_G_B_A CongA_G_B_A_D_E_F) as CongA_A_B_G_D_E_F.



	assert (~ eq G A) as n_eq_G_A.
	{
		intro eq_G_A.
		pose proof (lemma_equalitysymmetric _ _ eq_G_A) as eq_A_G.
		pose proof (lemma_s_col_eq_A_C A B G eq_A_G) as Col_A_B_G.
		contradict Col_A_B_G.
		exact n_Col_A_B_G.
	}
	assert (neq_G_A := n_eq_G_A).


	pose proof (lemma_extension G A G A neq_G_A neq_G_A) as (P & BetS_G_A_P & Cong_A_P_G_A).
	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (lemma_s_col_eq_B_C B A A eq_A_A) as Col_B_A_A.


	pose proof (lemma_samesidesymmetric _ _ _ _ SS_G_C_B_A) as (SS_C_G_B_A & _ & _).
	pose proof (lemma_s_os _ _ _ _ _ BetS_G_A_P Col_B_A_A nCol_B_A_G) as OS_G_B_A_P.
	pose proof (lemma_planeseparation _ _ _ _ _ SS_C_G_B_A OS_G_B_A_P) as OS_C_B_A_P.

	destruct OS_C_B_A_P as (R & BetS_C_R_P & Col_B_A_R & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_R_P) as BetS_P_R_C.

	(* assert by cases *)
	assert (LtA A B C D E F) as LtA_A_B_C_D_E_F.
	assert (OS G B C A \/ ~ OS G B C A) as [OS_G_B_C_A | n_OS_G_B_C_A] by (apply Classical_Prop.classic).
	{
		(* case OS_G_B_C_A *)

		destruct OS_G_B_C_A as (H & BetS_G_H_A & Col_B_C_H & nCol_B_C_G).
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_H_A) as BetS_A_H_G.
		pose proof (lemma_s_onray_assert_ABB B A neq_B_A) as OnRay_B_A_A.

		assert (~ Col A B H) as n_Col_A_B_H.
		{
			intro Col_A_B_H.

			assert (~ eq B H) as n_eq_B_H.
			{
				intro eq_B_H.
				assert (BetS A B G) as BetS_A_B_G by (rewrite eq_B_H; exact BetS_A_H_G).
				pose proof (lemma_s_col_BetS_A_B_C A B G BetS_A_B_G) as Col_A_B_G.
				pose proof (lemma_collinearorder _ _ _ Col_A_B_G) as (_ & _ & _ & _ & Col_G_B_A).
				pose proof (lemma_s_ncol_n_col _ _ _ nCol_G_B_A) as n_Col_G_B_A.
				contradict Col_G_B_A.
				exact n_Col_G_B_A.
			}
			assert (neq_B_H := n_eq_B_H).


			pose proof (lemma_inequalitysymmetric _ _ neq_B_H) as neq_H_B.
			pose proof (lemma_collinearorder _ _ _ Col_A_B_H) as (_ & _ & _ & _ & Col_H_B_A).
			pose proof (lemma_collinearorder _ _ _ Col_B_C_H) as (_ & _ & Col_H_B_C & _ & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_B_A Col_H_B_C neq_H_B) as Col_B_A_C.
			pose proof (lemma_collinearorder _ _ _ Col_B_A_C) as (Col_A_B_C & _ & _ & _ & _).
			contradict Col_A_B_C.
			exact n_Col_A_B_C.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_B_H) as nCol_A_B_H.
		pose proof (lemma_NCorder _ _ _ nCol_A_B_H) as (nCol_B_A_H & nCol_B_H_A & nCol_H_A_B & nCol_A_H_B & nCol_H_B_A).
		pose proof (lemma_s_ncol_n_col _ _ _ nCol_B_H_A) as n_Col_B_H_A.

		pose proof (lemma_equalanglesreflexive _ _ _ nCol_A_B_H) as CongA_A_B_H_A_B_H.
		pose proof (lemma_s_lta _ _ _ _ _ _ _ _ _ BetS_A_H_G OnRay_B_A_A OnRay_B_G_G CongA_A_B_H_A_B_H) as LtA_A_B_H_A_B_G.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_G_B_A) as CongA_G_B_A_A_B_G.
		pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_A_B_H_A_B_G CongA_G_B_A_A_B_G) as LtA_A_B_H_G_B_A.


		pose proof (lemma_ABCequalsCBA _ _ _ nCol_H_B_A) as CongA_H_B_A_A_B_H.
		pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_A_B_H_G_B_A CongA_H_B_A_A_B_H) as LtA_H_B_A_G_B_A.
		pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_H_B_A_G_B_A CongA_D_E_F_G_B_A) as LtA_H_B_A_D_E_F.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_B_H) as CongA_A_B_H_H_B_A.
		pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_H_B_A_D_E_F CongA_A_B_H_H_B_A) as LtA_A_B_H_D_E_F.
		
		pose proof (lemma_s_onray_assert_bets_AEB A G H BetS_A_H_G neq_A_G) as OnRay_A_G_H.

		pose proof (lemma_sameside2 _ _ _ _ _ _ SS_C_G_B_A Col_B_A_A OnRay_A_G_H) as SS_C_H_B_A.

		assert (~ BetS C B H) as n_BetS_C_B_H.
		{
			intro BetS_C_B_H.
			assert (eq B B) as eq_B_B by (reflexivity).
			pose proof (lemma_s_col_eq_A_C B A B eq_B_B) as Col_B_A_B.
			pose proof (lemma_s_os _ _ _ _ _ BetS_C_B_H Col_B_A_B nCol_B_A_C) as OS_C_B_A_H.
			pose proof (lemma_oppositesidesymmetric _ _ _ _ OS_C_B_A_H) as OS_H_B_A_C.
			pose proof (lemma_planeseparation _ _ _ _ _ SS_C_H_B_A OS_H_B_A_C) as OS_C_B_A_C.

			destruct OS_C_B_A_C as (M & BetS_C_M_C & Col_B_A_M & _).
			pose proof (axiom_betweennessidentity C M) as n_BetS_C_M_C.
			contradict BetS_C_M_C.
			exact n_BetS_C_M_C.
		}


		(* assert by cases *)
		assert (OnRay B C H) as OnRay_B_C_H.
		destruct Col_B_C_H as [eq_B_C | [eq_B_H | [eq_C_H | [BetS_C_B_H | [BetS_B_C_H | BetS_B_H_C]]]]].
		{
			(* case eq_B_C *)
			pose proof (lemma_s_col_eq_B_C A B C eq_B_C) as Col_A_B_C.
			contradict Col_A_B_C.
			exact n_Col_A_B_C.
		}
		{
			(* case eq_B_H *)
			pose proof (lemma_s_col_eq_A_B B H A eq_B_H) as Col_B_H_A.

			contradict Col_B_H_A.
			exact n_Col_B_H_A.
		}
		{
			(* case eq_C_H *)
			assert (eq H H) as eq_H_H by (reflexivity).

			(* assert by cases *)
			assert (OnRay B C H) as OnRay_B_C_H.
			assert (eq B H \/ neq B H) as [eq_B_H|neq_B_H] by (apply Classical_Prop.classic).
			{
				(* case eq_B_H *)
				pose proof (lemma_s_col_eq_A_B B H A eq_B_H) as Col_B_H_A.
				contradict Col_B_H_A.
				exact n_Col_B_H_A.
			}
			{
				(* case neq_B_H *)
				pose proof (lemma_s_onray_assert_ABB B H neq_B_H) as OnRay_B_H_H.
				assert (OnRay B C H) as OnRay_B_C_H by (rewrite eq_C_H; exact OnRay_B_H_H).

				exact OnRay_B_C_H.
			}

			exact OnRay_B_C_H.
		}
		{
			(* case BetS_C_B_H *)

			contradict BetS_C_B_H.
			exact n_BetS_C_B_H.
		}
		{
			(* case BetS_B_C_H *)
			pose proof (lemma_s_onray_assert_bets_ABE B C H BetS_B_C_H neq_B_C) as OnRay_B_C_H.

			exact OnRay_B_C_H.
		}
		{
			(* case BetS_B_H_C *)
			pose proof (lemma_s_onray_assert_bets_AEB B C H BetS_B_H_C neq_B_C) as OnRay_B_C_H.

			exact OnRay_B_C_H.
		}
		pose proof (lemma_equalanglesreflexive _ _ _ nCol_A_B_C) as CongA_A_B_C_A_B_C.
		pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_A_B_C_A_B_C OnRay_B_A_A OnRay_B_C_H) as CongA_A_B_C_A_B_H.
		pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_A_B_H_D_E_F CongA_A_B_C_A_B_H) as LtA_A_B_C_D_E_F.

		exact LtA_A_B_C_D_E_F.
	}
	{
		(* case n_OS_G_B_C_A *)

		(* assert by cases *)
		assert (LtA A B C D E F) as LtA_A_B_C_D_E_F.
		destruct Col_B_A_R as [eq_B_A | [eq_B_R | [eq_A_R | [BetS_A_B_R | [BetS_B_A_R | BetS_B_R_A]]]]].
		{
			(* case eq_B_A *)

			contradict eq_B_A.
			exact neq_B_A.
		}
		{
			(* case eq_B_R *)
			pose proof (lemma_equalitysymmetric _ _ eq_B_R) as eq_R_B.

			assert (~ Col C P G) as n_Col_C_P_G.
			{
				intro Col_C_P_G.
				pose proof (lemma_s_col_BetS_A_B_C C R P BetS_C_R_P) as Col_C_R_P.
				assert (Col C B P) as Col_C_B_P by (rewrite eq_B_R; exact Col_C_R_P).
				pose proof (lemma_s_col_BetS_A_B_C G A P BetS_G_A_P) as Col_G_A_P.
				pose proof (lemma_collinearorder _ _ _ Col_G_A_P) as (_ & _ & _ & Col_G_P_A & _).
				pose proof (lemma_collinearorder _ _ _ Col_C_P_G) as (_ & _ & _ & _ & Col_G_P_C).
				pose proof (lemma_betweennotequal _ _ _ BetS_G_A_P) as (_ & _ & neq_G_P).
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_P_C Col_G_P_A neq_G_P) as Col_P_C_A.
				pose proof (lemma_collinearorder _ _ _ Col_C_B_P) as (_ & _ & Col_P_C_B & _ & _).
				pose proof (lemma_betweennotequal _ _ _ BetS_C_R_P) as (_ & _ & neq_C_P).
				pose proof (lemma_inequalitysymmetric _ _ neq_C_P) as neq_P_C.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_P_C_A Col_P_C_B neq_P_C) as Col_C_A_B.
				pose proof (lemma_collinearorder _ _ _ Col_C_A_B) as (_ & Col_A_B_C & _ & _ & _).
				contradict Col_A_B_C.
				exact n_Col_A_B_C.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_C_P_G) as nCol_C_P_G.

			pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_C_R_P BetS_G_A_P nCol_C_P_G) as (Q & BetS_C_Q_A & BetS_G_Q_R).
			assert (BetS G Q B) as BetS_G_Q_B by (rewrite eq_B_R; exact BetS_G_Q_R).
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_Q_B) as BetS_B_Q_G.
			pose proof (lemma_betweennotequal _ _ _ BetS_B_Q_G) as (_ & neq_B_Q & _).
			
			pose proof (lemma_s_onray_assert_bets_ABE B Q G BetS_B_Q_G neq_B_Q) as OnRay_B_Q_G.

			pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_B_Q_G) as OnRay_B_G_Q.
			assert (eq Q Q) as eq_Q_Q by (reflexivity).
			assert (eq C C) as eq_C_C by (reflexivity).
			pose proof (lemma_s_onray_assert_ABB B A neq_B_A) as OnRay_B_A_A.
			pose proof (lemma_s_onray_assert_ABB B C neq_B_C) as OnRay_B_C_C.
			pose proof (lemma_s_onray_assert_ABB B Q neq_B_Q) as OnRay_B_Q_Q.
			pose proof (cn_congruencereflexive A Q) as Cong_A_Q_A_Q.
			pose proof (cn_congruencereflexive B Q) as Cong_B_Q_B_Q.
			pose proof (cn_congruencereflexive B A) as Cong_B_A_B_A.
			pose proof (lemma_s_conga _ _ _ _ _ _ _ _ _ _ OnRay_B_A_A OnRay_B_G_Q OnRay_B_A_A OnRay_B_Q_Q Cong_B_A_B_A Cong_B_Q_B_Q Cong_A_Q_A_Q nCol_A_B_G) as CongA_A_B_G_A_B_Q.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_Q_A) as BetS_A_Q_C.
			pose proof (lemma_s_lta _ _ _ _ _ _ _ _ _ BetS_A_Q_C OnRay_B_A_A OnRay_B_C_C CongA_A_B_G_A_B_Q) as LtA_A_B_G_A_B_C.
			pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_B_G_D_E_F) as CongA_D_E_F_A_B_G.
			pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_A_B_G_A_B_C CongA_D_E_F_A_B_G) as LtA_D_E_F_A_B_C.

			contradict LtA_D_E_F_A_B_C.
			exact n_LtA_D_E_F_A_B_C.
		}
		{
			(* case eq_A_R *)

			assert (~ ~ LtA A B C D E F) as n_n_LtA_A_B_C_D_E_F.
			{
				intro n_LtA_A_B_C_D_E_F.
				pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_A_P) as BetS_P_A_G.
				assert (BetS P A C) as BetS_P_A_C by (rewrite eq_A_R; exact BetS_P_R_C).
				pose proof (lemma_s_onray_assert_ABB B A neq_B_A) as OnRay_B_A_A.
				assert (eq C C) as eq_C_C by (reflexivity).
				pose proof (lemma_s_onray_assert_ABB B C neq_B_C) as OnRay_B_C_C.
				pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_B_G_D_E_F) as CongA_D_E_F_A_B_G.

				assert (~ BetS A G C) as n_BetS_A_G_C.
				{
					intro BetS_A_G_C.
					pose proof (lemma_equalanglesreflexive _ _ _ nCol_A_B_G) as CongA_A_B_G_A_B_G.
					pose proof (lemma_s_lta _ _ _ _ _ _ _ _ _ BetS_A_G_C OnRay_B_A_A OnRay_B_C_C CongA_A_B_G_A_B_G) as LtA_A_B_G_A_B_C.
					pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_A_B_G_A_B_C CongA_D_E_F_A_B_G) as LtA_D_E_F_A_B_C.
					contradict LtA_D_E_F_A_B_C.
					exact n_LtA_D_E_F_A_B_C.
				}


				assert (~ BetS A C G) as n_BetS_A_C_G.
				{
					intro BetS_A_C_G.
					pose proof (lemma_equalanglesreflexive _ _ _ nCol_A_B_C) as CongA_A_B_C_A_B_C.
					pose proof (lemma_s_lta _ _ _ _ _ _ _ _ _ BetS_A_C_G OnRay_B_A_A OnRay_B_G_G CongA_A_B_C_A_B_C) as LtA_A_B_C_A_B_G.
					pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_A_B_C_A_B_G CongA_D_E_F_A_B_G) as LtA_A_B_C_D_E_F.
					contradict LtA_A_B_C_D_E_F.
					exact n_LtA_A_B_C_D_E_F.
				}

				pose proof (lemma_outerconnectivity _ _ _ _ BetS_P_A_C BetS_P_A_G n_BetS_A_C_G n_BetS_A_G_C) as eq_C_G.
				pose proof (lemma_equalanglesreflexive _ _ _ nCol_A_B_C) as CongA_A_B_C_A_B_C.
				assert (CongA A B G A B C) as CongA_A_B_G_A_B_C by (rewrite <- eq_C_G; exact CongA_A_B_C_A_B_C).
				pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_B_G_A_B_C) as CongA_A_B_C_A_B_G.
				pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_B_C_A_B_G CongA_A_B_G_D_E_F) as CongA_A_B_C_D_E_F.
				contradict CongA_A_B_C_D_E_F.
				exact n_CongA_A_B_C_D_E_F.
			}
			assert (LtA_A_B_C_D_E_F := n_n_LtA_A_B_C_D_E_F).
			apply Classical_Prop.NNPP in LtA_A_B_C_D_E_F.

			exact LtA_A_B_C_D_E_F.
		}
		{
			(* case BetS_A_B_R *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_R) as BetS_R_B_A.

			assert (~ Col C P A) as n_Col_C_P_A.
			{
				intro Col_C_P_A.
				pose proof (lemma_s_col_BetS_A_B_C C R P BetS_C_R_P) as Col_C_R_P.
				pose proof (lemma_collinearorder _ _ _ Col_C_R_P) as (_ & _ & _ & Col_C_P_R & _).
				pose proof (lemma_betweennotequal _ _ _ BetS_C_R_P) as (_ & _ & neq_C_P).
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_P_A Col_C_P_R neq_C_P) as Col_P_A_R.
pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_B_R) as Col_A_B_R.
pose proof (lemma_collinearorder _ _ _ Col_A_B_R) as (Col_B_A_R & Col_B_R_A & Col_R_A_B & Col_A_R_B & Col_R_B_A).
				pose proof (lemma_collinearorder _ _ _ Col_P_A_R) as (_ & _ & _ & _ & Col_R_A_P).
				pose proof (lemma_betweennotequal _ _ _ BetS_A_B_R) as (_ & _& neq_A_R).
				pose proof (lemma_inequalitysymmetric _ _ neq_A_R) as neq_R_A.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_R_A_B Col_R_A_P neq_R_A) as Col_A_B_P.
				pose proof (lemma_collinearorder _ _ _ Col_A_B_P) as (_ & _ & Col_P_A_B & _ & _).
				pose proof (lemma_s_col_BetS_A_B_C G A P BetS_G_A_P) as Col_G_A_P.
				pose proof (lemma_collinearorder _ _ _ Col_G_A_P) as (_ & _ & _ & _ & Col_P_A_G).
				pose proof (lemma_betweennotequal _ _ _ BetS_G_A_P) as (neq_A_P & _ & _).
				pose proof (lemma_inequalitysymmetric _ _ neq_A_P) as neq_P_A.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_P_A_B Col_P_A_G neq_P_A) as Col_A_B_G.
				contradict Col_A_B_G.
				exact n_Col_A_B_G.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_C_P_A) as nCol_C_P_A.

			pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_A_B_R BetS_C_R_P nCol_C_P_A) as (M & BetS_A_M_P & BetS_C_B_M).
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_A_P) as BetS_P_A_G.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_M_P) as BetS_P_M_A.
			pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_P_M_A BetS_P_A_G) as BetS_M_A_G.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_M_A_G) as BetS_G_A_M.

			assert (~ Col C M G) as n_Col_C_M_G.
			{
				intro Col_C_M_G.
				pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_P_M_A BetS_P_A_G) as BetS_P_M_G.
				pose proof (lemma_s_col_BetS_A_B_C P M G BetS_P_M_G) as Col_P_M_G.
				pose proof (lemma_collinearorder _ _ _ Col_P_M_G) as (_ & Col_M_G_P & _ & _ & _).
				pose proof (lemma_collinearorder _ _ _ Col_C_M_G) as (_ & Col_M_G_C & _ & _ & _).
				pose proof (lemma_betweennotequal _ _ _ BetS_P_M_G) as (neq_M_G & _ & _).
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_M_G_P Col_M_G_C neq_M_G) as Col_G_P_C.
				pose proof (lemma_s_col_BetS_A_B_C P A G BetS_P_A_G) as Col_P_A_G.
				pose proof (lemma_collinearorder _ _ _ Col_P_A_G) as (_ & _ & Col_G_P_A & _ & _).
				pose proof (lemma_betweennotequal _ _ _ BetS_P_A_G) as (_ & _ & neq_P_G).
				pose proof (lemma_inequalitysymmetric _ _ neq_P_G) as neq_G_P.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_P_C Col_G_P_A neq_G_P) as Col_P_C_A.
				pose proof (lemma_collinearorder _ _ _ Col_P_C_A) as (Col_C_P_A & _ & _ & _ & _).
				contradict Col_C_P_A.
				exact n_Col_C_P_A.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_C_M_G) as nCol_C_M_G.

			pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_C_B_M BetS_G_A_M nCol_C_M_G) as (Q & BetS_C_Q_A & BetS_G_Q_B).
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_Q_B) as BetS_B_Q_G.
			pose proof (lemma_betweennotequal _ _ _ BetS_B_Q_G) as (_ & neq_B_Q & _).
			
			pose proof (lemma_s_onray_assert_bets_ABE B Q G BetS_B_Q_G neq_B_Q) as OnRay_B_Q_G.

			pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_B_Q_G) as OnRay_B_G_Q.
			assert (eq Q Q) as eq_Q_Q by (reflexivity).
			assert (eq C C) as eq_C_C by (reflexivity).
			pose proof (lemma_s_onray_assert_ABB B A neq_B_A) as OnRay_B_A_A.
			pose proof (lemma_s_onray_assert_ABB B C neq_B_C) as OnRay_B_C_C.
			pose proof (lemma_s_onray_assert_ABB B Q neq_B_Q) as OnRay_B_Q_Q.
			pose proof (cn_congruencereflexive A Q) as Cong_A_Q_A_Q.
			pose proof (cn_congruencereflexive B Q) as Cong_B_Q_B_Q.
			pose proof (cn_congruencereflexive B A) as Cong_B_A_B_A.
			pose proof (lemma_s_conga _ _ _ _ _ _ _ _ _ _ OnRay_B_A_A OnRay_B_G_Q OnRay_B_A_A OnRay_B_Q_Q Cong_B_A_B_A Cong_B_Q_B_Q Cong_A_Q_A_Q nCol_A_B_G) as CongA_A_B_G_A_B_Q.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_Q_A) as BetS_A_Q_C.
			pose proof (lemma_s_lta _ _ _ _ _ _ _ _ _ BetS_A_Q_C OnRay_B_A_A OnRay_B_C_C CongA_A_B_G_A_B_Q) as LtA_A_B_G_A_B_C.
			pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_B_G_D_E_F) as CongA_D_E_F_A_B_G.
			pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_A_B_G_A_B_C CongA_D_E_F_A_B_G) as LtA_D_E_F_A_B_C.

			contradict LtA_D_E_F_A_B_C.
			exact n_LtA_D_E_F_A_B_C.
		}
		{
			(* case BetS_B_A_R *)

			assert (~ Col P C B) as n_Col_P_C_B.
			{
				intro Col_P_C_B.
				pose proof (lemma_s_col_BetS_A_B_C B A R BetS_B_A_R) as Col_B_A_R.
				pose proof (lemma_s_col_BetS_A_B_C P R C BetS_P_R_C) as Col_P_R_C.
				pose proof (lemma_collinearorder _ _ _ Col_P_R_C) as (_ & _ & _ & Col_P_C_R & _).
				pose proof (lemma_betweennotequal _ _ _ BetS_P_R_C) as (_ & _ & neq_P_C).
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_P_C_B Col_P_C_R neq_P_C) as Col_C_B_R.
				pose proof (lemma_collinearorder _ _ _ Col_C_B_R) as (_ & _ & _ & _ & Col_R_B_C).
				pose proof (lemma_collinearorder _ _ _ Col_B_A_R) as (_ & _ & Col_R_B_A & _ & _).
				pose proof (lemma_betweennotequal _ _ _ BetS_B_A_R) as (_ & _ & neq_B_R).
				pose proof (lemma_inequalitysymmetric _ _ neq_B_R) as neq_R_B.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_R_B_C Col_R_B_A neq_R_B) as Col_B_C_A.
				pose proof (lemma_collinearorder _ _ _ Col_B_C_A) as (_ & _ & Col_A_B_C & _ & _).
				contradict Col_A_B_C.
				exact n_Col_A_B_C.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_P_C_B) as nCol_P_C_B.

			pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_B_A_R BetS_P_R_C nCol_P_C_B) as (Q & BetS_B_Q_C & BetS_P_A_Q).
			pose proof (lemma_s_col_BetS_A_C_B B C Q BetS_B_Q_C) as Col_B_C_Q.

			assert (~ eq G Q) as n_eq_G_Q.
			{
				intro eq_G_Q.
				assert (BetS B G C) as BetS_B_G_C by (rewrite eq_G_Q; exact BetS_B_Q_C).
				
				pose proof (lemma_s_onray_assert_bets_AEB B C G BetS_B_G_C neq_B_C) as OnRay_B_C_G.

				pose proof (lemma_s_onray_assert_ABB B A neq_B_A) as OnRay_B_A_A.
				pose proof (cn_congruencereflexive A G) as Cong_A_G_A_G.
				pose proof (cn_congruencereflexive B G) as Cong_B_G_B_G.
				pose proof (cn_congruencereflexive B A) as Cong_B_A_B_A.
				pose proof (lemma_s_conga _ _ _ _ _ _ _ _ _ _ OnRay_B_A_A OnRay_B_G_G OnRay_B_A_A OnRay_B_C_G Cong_B_A_B_A Cong_B_G_B_G Cong_A_G_A_G nCol_A_B_G) as CongA_A_B_G_A_B_C.
				pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_B_G_A_B_C) as CongA_A_B_C_A_B_G.
				pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_B_C_A_B_G CongA_A_B_G_D_E_F) as CongA_A_B_C_D_E_F.
				contradict CongA_A_B_C_D_E_F.
				exact n_CongA_A_B_C_D_E_F.
			}
			assert (neq_G_Q := n_eq_G_Q).

			assert (~ Col B C G) as n_Col_B_C_G.
			{
				intro Col_B_C_G.
				pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_A_P) as BetS_P_A_G.
				pose proof (lemma_s_onray _ _ _ _ BetS_P_A_G BetS_P_A_Q) as OnRay_A_G_Q.
				pose proof (lemma_onray_impliescollinear _ _ _ OnRay_A_G_Q) as Col_A_G_Q.
				pose proof (lemma_collinearorder _ _ _ Col_B_C_Q) as (_ & _ & _ & _ & Col_Q_C_B).
				pose proof (lemma_collinearorder _ _ _ Col_B_C_G) as (Col_C_B_G & _ & _ & _ & _).
				pose proof (lemma_collinearorder _ _ _ Col_B_C_Q) as (Col_C_B_Q & _ & _ & _ & _).
				pose proof (lemma_inequalitysymmetric _ _ neq_B_C) as neq_C_B.
				assert (eq B B) as eq_B_B by (reflexivity).
				pose proof (lemma_s_col_eq_B_C C B B eq_B_B) as Col_C_B_B.
				pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_C_B Col_C_B_G Col_C_B_Q Col_C_B_B) as Col_G_Q_B.
				pose proof (lemma_collinearorder _ _ _ Col_G_Q_B) as (Col_Q_G_B & _ & _ & _ & _).
				pose proof (lemma_collinearorder _ _ _ Col_A_G_Q) as (_ & _ & _ & _ & Col_Q_G_A).
				pose proof (lemma_inequalitysymmetric _ _ neq_G_Q) as neq_Q_G.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_G_B Col_Q_G_A neq_Q_G) as Col_G_B_A.
				pose proof (lemma_collinearorder _ _ _ Col_G_B_A) as (_ & _ & _ & _ & Col_A_B_G).
				contradict Col_A_B_G.
				exact n_Col_A_B_G.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_B_C_G) as nCol_B_C_G.


			assert (~ BetS A Q G) as n_BetS_A_Q_G.
			{
				intro BetS_A_Q_G.
				pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_Q_G) as BetS_G_Q_A.
				pose proof (lemma_s_os _ _ _ _ _ BetS_G_Q_A Col_B_C_Q nCol_B_C_G) as OS_G_B_C_A.
				contradict OS_G_B_C_A.
				exact n_OS_G_B_C_A.
			}

			
			pose proof (lemma_s_onray_assert_bets_AEB B C Q BetS_B_Q_C neq_B_C) as OnRay_B_C_Q.

			pose proof (lemma_s_onray_assert_ABB B A neq_B_A) as OnRay_B_A_A.

			assert (~ BetS A G Q) as n_BetS_A_G_Q.
			{
				intro BetS_A_G_Q.
				pose proof (lemma_equalanglesreflexive _ _ _ nCol_A_B_G) as CongA_A_B_G_A_B_G.
				pose proof (lemma_s_lta _ _ _ _ _ _ _ _ _ BetS_A_G_Q OnRay_B_A_A OnRay_B_C_Q CongA_A_B_G_A_B_G) as LtA_A_B_G_A_B_C.
				pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_B_G_D_E_F) as CongA_D_E_F_A_B_G.
				pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_A_B_G_A_B_C CongA_D_E_F_A_B_G) as LtA_D_E_F_A_B_C.
				contradict LtA_D_E_F_A_B_C.
				exact n_LtA_D_E_F_A_B_C.
			}

			pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_A_P) as BetS_P_A_G.
			pose proof (lemma_outerconnectivity _ _ _ _ BetS_P_A_G BetS_P_A_Q n_BetS_A_G_Q n_BetS_A_Q_G) as eq_G_Q.

			contradict eq_G_Q.
			exact neq_G_Q.
		}
		{
			(* case BetS_B_R_A *)

			assert (~ ~ LtA A B C D E F) as n_n_LtA_A_B_C_D_E_F.
			{
				intro n_LtA_A_B_C_D_E_F.
				pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_A_P) as BetS_P_A_G.

				assert (~ Col P G B) as n_Col_P_G_B.
				{
					intro Col_P_G_B.
					pose proof (lemma_s_col_BetS_A_B_C P A G BetS_P_A_G) as Col_P_A_G.
					pose proof (lemma_collinearorder _ _ _ Col_P_A_G) as (_ & _ & _ & Col_P_G_A & _).
					pose proof (lemma_betweennotequal _ _ _ BetS_P_A_G) as (_ & _ & neq_P_G).
					pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_P_G_B Col_P_G_A neq_P_G) as Col_G_B_A.
					pose proof (lemma_collinearorder _ _ _ Col_G_B_A) as (_ & _ & _ & _ & Col_A_B_G).
					contradict Col_A_B_G.
					exact n_Col_A_B_G.
				}
				pose proof (lemma_s_n_col_ncol _ _ _ n_Col_P_G_B) as nCol_P_G_B.

				pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_B_R_A BetS_P_A_G nCol_P_G_B) as (Q & BetS_B_Q_G & BetS_P_R_Q).
				pose proof (lemma_betweennotequal _ _ _ BetS_B_Q_G) as (neq_Q_G & _ & _).
				pose proof (lemma_betweennotequal _ _ _ BetS_B_Q_G) as (_ & neq_B_Q & _).
				pose proof (lemma_s_onray_assert_ABB B A neq_B_A) as OnRay_B_A_A.
				
				pose proof (lemma_s_onray_assert_bets_AEB B G Q BetS_B_Q_G neq_B_G) as OnRay_B_G_Q.
				pose proof (lemma_s_onray_assert_bets_ABE B Q G BetS_B_Q_G neq_B_Q) as OnRay_B_Q_G.


				assert (~ BetS R C Q) as n_BetS_R_C_Q.
				{
					intro BetS_R_C_Q.
					
					pose proof (lemma_s_onray_assert_bets_AEB B A R BetS_B_R_A neq_B_A) as OnRay_B_A_R.

					pose proof (lemma_equalanglesreflexive _ _ _ nCol_A_B_C) as CongA_A_B_C_A_B_C.
					pose proof (lemma_s_lta _ _ _ _ _ _ _ _ _ BetS_R_C_Q OnRay_B_A_R OnRay_B_G_Q CongA_A_B_C_A_B_C) as LtA_A_B_C_A_B_G.
					pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_B_G_D_E_F) as CongA_D_E_F_A_B_G.
					pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_A_B_C_A_B_G CongA_D_E_F_A_B_G) as LtA_A_B_C_D_E_F.
					contradict LtA_A_B_C_D_E_F.
					exact n_LtA_A_B_C_D_E_F.
				}


				assert (~ BetS R Q C) as n_BetS_R_Q_C.
				{
					intro BetS_R_Q_C.
					

					pose proof (cn_congruencereflexive B A) as Cong_B_A_B_A.
					pose proof (cn_congruencereflexive B G) as Cong_B_G_B_G.
					pose proof (cn_congruencereflexive A G) as Cong_A_G_A_G.
					pose proof (lemma_s_conga _ _ _ _ _ _ _ _ _ _ OnRay_B_A_A OnRay_B_G_G OnRay_B_A_A OnRay_B_Q_G Cong_B_A_B_A Cong_B_G_B_G Cong_A_G_A_G nCol_A_B_G) as CongA_A_B_G_A_B_Q.
					
					pose proof (lemma_s_onray_assert_bets_AEB B A R BetS_B_R_A neq_B_A) as OnRay_B_A_R.

					assert (eq C C) as eq_C_C by (reflexivity).
					pose proof (lemma_s_onray_assert_ABB B C neq_B_C) as OnRay_B_C_C.
					pose proof (lemma_s_lta _ _ _ _ _ _ _ _ _ BetS_R_Q_C OnRay_B_A_R OnRay_B_C_C CongA_A_B_G_A_B_Q) as LtA_A_B_G_A_B_C.
					pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_B_G_D_E_F) as CongA_D_E_F_A_B_G.
					pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_A_B_G_A_B_C CongA_D_E_F_A_B_G) as LtA_D_E_F_A_B_C.
					contradict LtA_D_E_F_A_B_C.
					exact n_LtA_D_E_F_A_B_C.
				}

				pose proof (lemma_outerconnectivity _ _ _ _ BetS_P_R_Q BetS_P_R_C n_BetS_R_Q_C n_BetS_R_C_Q) as eq_Q_C.
				assert (eq C C) as eq_C_C by (reflexivity).
				pose proof (lemma_s_onray_assert_ABB B C neq_B_C) as OnRay_B_C_C.
				assert (OnRay B C G) as OnRay_B_C_G by (rewrite <- eq_Q_C; exact OnRay_B_Q_G).
				
				pose proof (cn_congruencereflexive B A) as Cong_B_A_B_A.
				pose proof (cn_congruencereflexive B G) as Cong_B_G_B_G.
				pose proof (cn_congruencereflexive A G) as Cong_A_G_A_G.
				pose proof (lemma_s_conga _ _ _ _ _ _ _ _ _ _ OnRay_B_A_A OnRay_B_G_G OnRay_B_A_A OnRay_B_Q_G Cong_B_A_B_A Cong_B_G_B_G Cong_A_G_A_G nCol_A_B_G) as CongA_A_B_G_A_B_Q.
				pose proof (lemma_s_conga _ _ _ _ _ _ _ _ _ _ OnRay_B_A_A OnRay_B_C_G OnRay_B_A_A OnRay_B_G_G Cong_B_A_B_A Cong_B_G_B_G Cong_A_G_A_G nCol_A_B_C) as CongA_A_B_C_A_B_G.
				pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_B_C_A_B_G CongA_A_B_G_D_E_F) as CongA_A_B_C_D_E_F.
				contradict CongA_A_B_C_D_E_F.
				exact n_CongA_A_B_C_D_E_F.
			}
			assert (LtA_A_B_C_D_E_F := n_n_LtA_A_B_C_D_E_F).
			apply Classical_Prop.NNPP in LtA_A_B_C_D_E_F.

			exact LtA_A_B_C_D_E_F.
		}

		exact LtA_A_B_C_D_E_F.
	}
	exact LtA_A_B_C_D_E_F.
Qed.

End Euclid.
