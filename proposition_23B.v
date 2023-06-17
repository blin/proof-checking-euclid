Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_otherside_onray_PABC_RQP_QABC.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_Euclid4.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_collinearright.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalanglesflip.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_right_triangle_NC.
Require Import ProofCheckingEuclid.lemma_right_triangle_leg_change.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
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
Require Import ProofCheckingEuclid.lemma_s_supp.
Require Import ProofCheckingEuclid.lemma_s_triangle.
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
	exists X Y, OnRay A B Y /\ CongA X A Y D C E /\ OS X A B P.
Proof.
	intros A B C D E P.
	intros neq_A_B.
	intros nCol_D_C_E.
	intros nCol_A_B_P.

	pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.
	pose proof (proposition_23 _ _ _ _ _ neq_A_B nCol_D_C_E) as (F & G & OnRay_A_B_G & CongA_F_A_G_D_C_E).
	pose proof (lemma_onray_strict _ _ _ OnRay_A_B_G) as neq_A_G.

	assert (~ Col A B F) as n_Col_A_B_F.
	{
		intro Col_A_B_F.
		pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_F_A_G_D_C_E) as CongA_D_C_E_F_A_G.
		pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_D_C_E_F_A_G) as nCol_F_A_G.
		pose proof (lemma_s_ncol_n_col _ _ _ nCol_F_A_G) as n_Col_F_A_G.
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_A_B_G) as Col_A_B_G.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_F Col_A_B_G neq_A_B) as Col_B_F_G.
		pose proof (lemma_collinearorder _ _ _ Col_A_B_F) as (_ & Col_B_F_A & _ & _ & _).

		assert (~ eq F B) as n_eq_F_B.
		{
			intro eq_F_B.
			assert (OnRay A F G) as OnRay_A_F_G by (rewrite eq_F_B; exact OnRay_A_B_G).
			pose proof (lemma_onray_impliescollinear _ _ _ OnRay_A_F_G) as Col_A_F_G.
			pose proof (lemma_collinearorder _ _ _ Col_A_F_G) as (Col_F_A_G & _ & _ & _ & _).
			contradict Col_F_A_G.
			exact n_Col_F_A_G.
		}
		assert (neq_F_B := n_eq_F_B).


		pose proof (lemma_inequalitysymmetric _ _ neq_F_B) as neq_B_F.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_F_A Col_B_F_G neq_B_F) as Col_F_A_G.
		contradict Col_F_A_G.
		exact n_Col_F_A_G.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_B_F) as nCol_A_B_F.

	pose proof (proposition_12 _ _ _ nCol_A_B_F) as (H & Perp_at_F_H_A_B_H).

	destruct Perp_at_F_H_A_B_H as (J & Col_F_H_H & Col_A_B_H & Col_A_B_J & RightTriangle_J_H_F).
	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_J_H_F) as nCol_J_H_F.

	assert (~ eq F H) as n_eq_F_H.
	{
		intro eq_F_H.
		assert (Col A B F) as Col_A_B_F by (rewrite eq_F_H; exact Col_A_B_H).
		contradict Col_A_B_F.
		exact n_Col_A_B_F.
	}
	assert (neq_F_H := n_eq_F_H).


	pose proof (lemma_s_ncol_n_col _ _ _ nCol_J_H_F) as n_Col_J_H_F.

	assert (~ eq J H) as n_eq_J_H.
	{
		intro eq_J_H.
		pose proof (lemma_s_col_eq_A_B J H F eq_J_H) as Col_J_H_F.
		contradict Col_J_H_F.
		exact n_Col_J_H_F.
	}
	assert (neq_J_H := n_eq_J_H).


	pose proof (lemma_inequalitysymmetric _ _ neq_J_H) as neq_H_J.
	pose proof (lemma_extension J H H J neq_J_H neq_H_J) as (T & BetS_J_H_T & Cong_H_T_H_J).
	pose proof (lemma_s_col_BetS_A_B_C J H T BetS_J_H_T) as Col_J_H_T.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_J Col_A_B_H neq_A_B) as Col_B_J_H.
	pose proof (lemma_betweennotequal _ _ _ BetS_J_H_T) as (_ & _ & neq_J_T).
	pose proof (lemma_collinearorder _ _ _ Col_B_J_H) as (_ & _ & _ & _ & Col_H_J_B).
	pose proof (lemma_collinearorder _ _ _ Col_J_H_T) as (Col_H_J_T & _ & _ & _ & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_J_B Col_H_J_T neq_H_J) as Col_J_B_T.
	pose proof (lemma_collinearorder _ _ _ Col_J_B_T) as (_ & _ & _ & Col_J_T_B & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_J) as (Col_B_A_J & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_H) as (Col_B_A_H & _ & _ & _ & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_J Col_B_A_H neq_B_A) as Col_A_J_H.
	pose proof (lemma_collinearorder _ _ _ Col_A_J_H) as (_ & _ & _ & _ & Col_H_J_A).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_J_A Col_H_J_T neq_H_J) as Col_J_A_T.
	pose proof (lemma_collinearorder _ _ _ Col_J_A_T) as (_ & _ & _ & Col_J_T_A & _).

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_P) as n_Col_A_B_P.

	assert (~ Col J T P) as n_Col_J_T_P.
	{
		intro Col_J_T_P.
		pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_J_T Col_J_T_A Col_J_T_B Col_J_T_P) as Col_A_B_P.
		contradict Col_A_B_P.
		exact n_Col_A_B_P.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_J_T_P) as nCol_J_T_P.

	pose proof (proposition_11B _ _ _ _ BetS_J_H_T nCol_J_T_P) as (Q & RightTriangle_J_H_Q & OS_Q_J_T_P).
	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_J_H_Q) as nCol_J_H_Q.

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_J_H_Q) as n_Col_J_H_Q.

	assert (~ eq H Q) as n_eq_H_Q.
	{
		intro eq_H_Q.
		pose proof (lemma_s_col_eq_B_C J H Q eq_H_Q) as Col_J_H_Q.
		contradict Col_J_H_Q.
		exact n_Col_J_H_Q.
	}
	assert (neq_H_Q := n_eq_H_Q).



	assert (~ eq H F) as n_eq_H_F.
	{
		intro eq_H_F.
		pose proof (lemma_s_col_eq_B_C J H F eq_H_F) as Col_J_H_F.
		contradict Col_J_H_F.
		exact n_Col_J_H_F.
	}
	assert (neq_H_F := n_eq_H_F).


	pose proof (lemma_layoff _ _ _ _ neq_H_Q neq_H_F) as (S & OnRay_H_Q_S & Cong_H_S_H_F).
	assert (eq F F) as eq_F_F by (reflexivity).
	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_F_A_G_D_C_E) as (_ & _ & _ & neq_D_C & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_D_C) as neq_C_D.
	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_F_A_G_D_C_E) as (_ & _ & _ & _ & neq_C_E & _).
	pose proof (lemma_collinearorder _ _ _ Col_H_J_A) as (Col_J_H_A & _ & _ & _ & _).
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_J_H_Q OnRay_H_Q_S) as RightTriangle_J_H_S.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_J_H_S) as RightTriangle_S_H_J.
	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_J_H_F RightTriangle_J_H_S) as CongA_J_H_F_J_H_S.
	assert (eq S S) as eq_S_S by (reflexivity).
	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_J_H_F_J_H_S) as (_ & _ & _ & _ & neq_H_S & _).

	(* assert by cases *)
	assert (CongA F A G S A G) as CongA_F_A_G_S_A_G.
	assert (eq A H \/ neq A H) as [eq_A_H|neq_A_H] by (apply Classical_Prop.classic).
	{
		(* case eq_A_H *)
		assert (RightTriangle J A F) as RightTriangle_J_A_F by (rewrite eq_A_H; exact RightTriangle_J_H_F).
		assert (RightTriangle J A S) as RightTriangle_J_A_S by (rewrite eq_A_H; exact RightTriangle_J_H_S).
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_A_B_G) as Col_A_B_G.
		pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_A_B Col_A_B_J Col_A_B_H Col_A_B_G) as Col_J_H_G.
		assert (Col J A G) as Col_J_A_G by (rewrite eq_A_H; exact Col_J_H_G).
		pose proof (lemma_inequalitysymmetric _ _ neq_A_G) as neq_G_A.
		pose proof (lemma_collinearright _ _ _ _ RightTriangle_J_A_F Col_J_A_G neq_G_A) as RightTriangle_G_A_F.
		pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_G_A_F) as RightTriangle_F_A_G.
		pose proof (lemma_collinearright _ _ _ _ RightTriangle_J_A_S Col_J_A_G neq_G_A) as RightTriangle_G_A_S.
		pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_G_A_S) as RightTriangle_S_A_G.
		pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_F_A_G RightTriangle_S_A_G) as CongA_F_A_G_S_A_G.

		exact CongA_F_A_G_S_A_G.
	}
	{
		(* case neq_A_H *)
		pose proof (lemma_doublereverse _ _ _ _ Cong_H_S_H_F) as (Cong_F_H_S_H & _).
		pose proof (lemma_collinearright _ _ _ _ RightTriangle_J_H_F Col_J_H_A neq_A_H) as RightTriangle_A_H_F.
		pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_A_H_F) as RightTriangle_F_H_A.
		pose proof (lemma_collinearright _ _ _ _ RightTriangle_J_H_S Col_J_H_A neq_A_H) as RightTriangle_A_H_S.
		pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_A_H_F RightTriangle_A_H_S) as CongA_A_H_F_A_H_S.
		pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_F_H_A) as nCol_F_H_A.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_F_H_A) as CongA_F_H_A_A_H_F.
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_F_H_A_A_H_F CongA_A_H_F_A_H_S) as CongA_F_H_A_A_H_S.
		pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_A_H_S) as nCol_A_H_S.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_H_S) as CongA_A_H_S_S_H_A.
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_F_H_A_A_H_S CongA_A_H_S_S_H_A) as CongA_F_H_A_S_H_A.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_F_H_S_H) as (Cong_H_F_H_S & _ & _).
		pose proof (cn_congruencereflexive H A) as Cong_H_A_H_A.

		pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_H_S) as n_Col_A_H_S.

		assert (~ Col S H A) as n_Col_S_H_A.
		{
			intro Col_S_H_A.
			pose proof (lemma_collinearorder _ _ _ Col_S_H_A) as (_ & _ & _ & _ & Col_A_H_S).
			contradict Col_A_H_S.
			exact n_Col_A_H_S.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_S_H_A) as nCol_S_H_A.

		pose proof (proposition_04 _ _ _ _ _ _ Cong_H_F_H_S Cong_H_A_H_A CongA_F_H_A_S_H_A) as (Cong_F_A_S_A & CongA_H_F_A_H_S_A & CongA_H_A_F_H_A_S).


		pose proof (lemma_s_ncol_n_col _ _ _ nCol_F_H_A) as n_Col_F_H_A.

		assert (~ Col F A H) as n_Col_F_A_H.
		{
			intro Col_F_A_H.
			pose proof (lemma_collinearorder _ _ _ Col_F_A_H) as (_ & _ & _ & Col_F_H_A & _).
			contradict Col_F_H_A.
			exact n_Col_F_H_A.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_F_A_H) as nCol_F_A_H.

		pose proof (lemma_ABCequalsCBA _ _ _ nCol_F_A_H) as CongA_F_A_H_H_A_F.


		assert (~ Col H A S) as n_Col_H_A_S.
		{
			intro Col_H_A_S.
			pose proof (lemma_collinearorder _ _ _ Col_H_A_S) as (_ & _ & Col_S_H_A & _ & _).
			contradict Col_S_H_A.
			exact n_Col_S_H_A.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_H_A_S) as nCol_H_A_S.

		pose proof (lemma_ABCequalsCBA _ _ _ nCol_H_A_S) as CongA_H_A_S_S_A_H.
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_F_A_H_H_A_F CongA_H_A_F_H_A_S) as CongA_F_A_H_H_A_S.
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_F_A_H_H_A_S CongA_H_A_S_S_A_H) as CongA_F_A_H_S_A_H.
		assert (eq A A) as eq_A_A by (reflexivity).
		pose proof (lemma_s_col_eq_A_C A B A eq_A_A) as Col_A_B_A.
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_A_B_G) as Col_A_B_G.

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
		pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_F_A_G_D_C_E) as (neq_F_A & _ & _ & _ & _ & _).
		pose proof (lemma_inequalitysymmetric _ _ neq_F_A) as neq_A_F.
		pose proof (lemma_s_onray_assert_ABB A F neq_A_F) as OnRay_A_F_F.
		pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_H_A_S_S_A_H) as (_ & _ & _ & neq_S_A & _ & _).
		pose proof (lemma_inequalitysymmetric _ _ neq_S_A) as neq_A_S.
		pose proof (lemma_s_onray_assert_ABB A S neq_A_S) as OnRay_A_S_S.

		(* assert by cases *)
		assert (CongA F A G S A G) as CongA_F_A_G_S_A_G.
		destruct Col_G_H_A as [eq_G_H | [eq_G_A | [eq_H_A | [BetS_H_G_A | [BetS_G_H_A | BetS_G_A_H]]]]].
		{
			(* case eq_G_H *)

			assert (~ ~ CongA F A G S A G) as n_n_CongA_F_A_G_S_A_G.
			{
				intro n_CongA_F_A_G_S_A_G.
				assert (CongA F A G S A G) as CongA_F_A_G_S_A_G by (rewrite eq_G_H; exact CongA_F_A_H_S_A_H).
				contradict CongA_F_A_G_S_A_G.
				exact n_CongA_F_A_G_S_A_G.
			}
			assert (CongA_F_A_G_S_A_G := n_n_CongA_F_A_G_S_A_G).
			apply Classical_Prop.NNPP in CongA_F_A_G_S_A_G.


			exact CongA_F_A_G_S_A_G.
		}
		{
			(* case eq_G_A *)

			assert (~ ~ CongA F A G S A G) as n_n_CongA_F_A_G_S_A_G.
			{
				intro n_CongA_F_A_G_S_A_G.
				pose proof (lemma_inequalitysymmetric _ _ neq_A_G) as neq_G_A.
				contradict eq_G_A.
				exact neq_G_A.
			}
			assert (CongA_F_A_G_S_A_G := n_n_CongA_F_A_G_S_A_G).
			apply Classical_Prop.NNPP in CongA_F_A_G_S_A_G.


			exact CongA_F_A_G_S_A_G.
		}
		{
			(* case eq_H_A *)

			assert (~ ~ CongA F A G S A G) as n_n_CongA_F_A_G_S_A_G.
			{
				intro n_CongA_F_A_G_S_A_G.
				pose proof (lemma_inequalitysymmetric _ _ neq_A_H) as neq_H_A.
				contradict eq_H_A.
				exact neq_H_A.
			}
			assert (CongA_F_A_G_S_A_G := n_n_CongA_F_A_G_S_A_G).
			apply Classical_Prop.NNPP in CongA_F_A_G_S_A_G.


			exact CongA_F_A_G_S_A_G.
		}
		{
			(* case BetS_H_G_A *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_G_A) as BetS_A_G_H.
			
			pose proof (lemma_s_onray_assert_bets_AEB A H G BetS_A_G_H neq_A_H) as OnRay_A_H_G.

			pose proof (lemma_equalanglesreflexive _ _ _ nCol_F_A_H) as CongA_F_A_H_F_A_H.

			assert (~ Col S A H) as n_Col_S_A_H.
			{
				intro Col_S_A_H.
				pose proof (lemma_collinearorder _ _ _ Col_S_A_H) as (_ & _ & _ & Col_S_H_A & _).
				contradict Col_S_H_A.
				exact n_Col_S_H_A.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_S_A_H) as nCol_S_A_H.

			pose proof (lemma_equalanglesreflexive _ _ _ nCol_S_A_H) as CongA_S_A_H_S_A_H.
			pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_F_A_H_F_A_H OnRay_A_F_F OnRay_A_H_G) as CongA_F_A_H_F_A_G.
			pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_S_A_H_S_A_H OnRay_A_S_S OnRay_A_H_G) as CongA_S_A_H_S_A_G.
			pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_F_A_H_F_A_G) as CongA_F_A_G_F_A_H.
			pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_F_A_G_F_A_H CongA_F_A_H_S_A_H) as CongA_F_A_G_S_A_H.
			pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_F_A_G_S_A_H CongA_S_A_H_S_A_G) as CongA_F_A_G_S_A_G.

			exact CongA_F_A_G_S_A_G.
		}
		{
			(* case BetS_G_H_A *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_H_A) as BetS_A_H_G.
			
			pose proof (lemma_s_onray_assert_bets_ABE A H G BetS_A_H_G neq_A_H) as OnRay_A_H_G.

			pose proof (lemma_equalanglesreflexive _ _ _ nCol_F_A_H) as CongA_F_A_H_F_A_H.

			assert (~ Col S A H) as n_Col_S_A_H.
			{
				intro Col_S_A_H.
				pose proof (lemma_collinearorder _ _ _ Col_S_A_H) as (_ & _ & _ & Col_S_H_A & _).
				contradict Col_S_H_A.
				exact n_Col_S_H_A.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_S_A_H) as nCol_S_A_H.

			pose proof (lemma_equalanglesreflexive _ _ _ nCol_S_A_H) as CongA_S_A_H_S_A_H.
			pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_F_A_H_F_A_H OnRay_A_F_F OnRay_A_H_G) as CongA_F_A_H_F_A_G.
			pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_S_A_H_S_A_H OnRay_A_S_S OnRay_A_H_G) as CongA_S_A_H_S_A_G.
			pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_F_A_H_F_A_G) as CongA_F_A_G_F_A_H.
			pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_F_A_G_F_A_H CongA_F_A_H_S_A_H) as CongA_F_A_G_S_A_H.
			pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_F_A_G_S_A_H CongA_S_A_H_S_A_G) as CongA_F_A_G_S_A_G.

			exact CongA_F_A_G_S_A_G.
		}
		{
			(* case BetS_G_A_H *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_A_H) as BetS_H_A_G.
			pose proof (lemma_s_supp _ _ _ _ _ OnRay_A_F_F BetS_H_A_G) as Supp_H_A_F_F_G.
			pose proof (lemma_s_supp _ _ _ _ _ OnRay_A_S_S BetS_H_A_G) as Supp_H_A_S_S_G.
			pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_H_A_F_H_A_S Supp_H_A_F_F_G Supp_H_A_S_S_G) as CongA_F_A_G_S_A_G.

			exact CongA_F_A_G_S_A_G.
		}

		exact CongA_F_A_G_S_A_G.
	}
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_F_A_G_S_A_G) as CongA_S_A_G_F_A_G.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_S_A_G_F_A_G CongA_F_A_G_D_C_E) as CongA_S_A_G_D_C_E.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_H_Q_S) as OnRay_H_S_Q.
	pose proof (lemma_collinearorder _ _ _ Col_H_J_T) as (_ & Col_J_T_H & _ & _ & _).
	pose proof (lemma_otherside_onray_PABC_RQP_QABC _ _ _ _ _ _ OS_Q_J_T_P OnRay_H_S_Q Col_J_T_H) as OS_S_J_T_P.

	destruct OS_S_J_T_P as (M & BetS_S_M_P & Col_J_T_M & nCol_J_T_S).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_J_T_A Col_J_T_B neq_J_T) as Col_T_A_B.
	pose proof (lemma_collinearorder _ _ _ Col_T_A_B) as (_ & Col_A_B_T & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_T) as (Col_B_A_T & _ & _ & _ & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_J Col_B_A_T neq_B_A) as Col_A_J_T.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_J Col_A_B_T neq_A_B) as Col_B_J_T.
	pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_J_T Col_J_T_A Col_J_T_B Col_J_T_M) as Col_A_B_M.

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_J_T_S) as n_Col_J_T_S.

	assert (~ Col A B S) as n_Col_A_B_S.
	{
		intro Col_A_B_S.
		pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_A_B Col_A_B_J Col_A_B_T Col_A_B_S) as Col_J_T_S.
		contradict Col_J_T_S.
		exact n_Col_J_T_S.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_B_S) as nCol_A_B_S.

	pose proof (lemma_s_os _ _ _ _ _ BetS_S_M_P Col_A_B_M nCol_A_B_S) as OS_S_A_B_P.

	exists S, G.
	split.
	exact OnRay_A_B_G.
	split.
	exact CongA_S_A_G_D_C_E.
	exact OS_S_A_B_P.
Qed.

End Euclid.
