Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NChelper.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_collinearparallel.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABD_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_parallelNC.
Require Import ProofCheckingEuclid.lemma_paralleldef2B.
Require Import ProofCheckingEuclid.lemma_parallelflip.
Require Import ProofCheckingEuclid.lemma_parallelsymmetric.
Require Import ProofCheckingEuclid.lemma_planeseparation.
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
Require Import ProofCheckingEuclid.lemma_s_par.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_crisscross :
	forall A B C D,
	Par A C B D ->
	~ Cross A B C D ->
	Cross A D B C.
Proof.
	intros A B C D.
	intros Par_A_C_B_D.
	intros n_Cross_A_B_C_D.

	pose proof (lemma_parallelsymmetric _ _ _ _ Par_A_C_B_D) as Par_B_D_A_C.
	pose proof (lemma_paralleldef2B _ _ _ _ Par_B_D_A_C) as TarskiPar_B_D_A_C.

	destruct TarskiPar_B_D_A_C as (neq_B_D & neq_A_C & n_Meet_B_D_A_C & SS_A_C_B_D).

	pose proof (lemma_parallelNC _ _ _ _ Par_A_C_B_D) as (nCol_A_C_B & _ & _ & _).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_C_B) as (_ & _ & neq_A_B & _ & _ & _).
	pose proof (lemma_extension A B A B neq_A_B neq_A_B) as (E & BetS_A_B_E & Cong_B_E_A_B).
	assert (eq B B) as eq_B_B by (reflexivity).
	pose proof (lemma_s_col_eq_A_C B D B eq_B_B) as Col_B_D_B.
	pose proof (lemma_parallelNC _ _ _ _ Par_A_C_B_D) as (_ & nCol_A_B_D & _ & _).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_D) as (_ & nCol_B_D_A & _ & _ & _).
	pose proof (lemma_samesidesymmetric _ _ _ _ SS_A_C_B_D) as (SS_C_A_B_D & _ & _).
	pose proof (lemma_s_os _ _ _ _ _ BetS_A_B_E Col_B_D_B nCol_B_D_A) as OS_A_B_D_E.
	pose proof (lemma_planeseparation _ _ _ _ _ SS_C_A_B_D OS_A_B_D_E) as OS_C_B_D_E.

	destruct OS_C_B_D_E as (F & BetS_C_F_E & Col_B_D_F & nCol_B_D_C).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_D) as (_ & _ & neq_A_D & _ & _ & _).
	pose proof (lemma_parallelNC _ _ _ _ Par_A_C_B_D) as (_ & _ & _ & nCol_A_C_D).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_C_D) as (_ & neq_C_D & _ & _ & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_C) as neq_C_A.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_C_B) as (_ & neq_C_B & _ & _ & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_C_B) as neq_B_C.

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_C_B) as n_Col_A_C_B.


	(* assert by cases *)
	assert (Cross A D B C) as Cross_A_D_B_C.
	assert (Col_B_D_F_2 := Col_B_D_F).
	destruct Col_B_D_F_2 as [eq_B_D | [eq_B_F | [eq_D_F | [BetS_D_B_F | [BetS_B_D_F | BetS_B_F_D]]]]].
	{
		(* case eq_B_D *)
		contradict eq_B_D.
		exact neq_B_D.
	}
	{
		(* case eq_B_F *)

		assert (~ ~ Cross A D B C) as n_n_Cross_A_D_B_C.
		{
			intro n_Cross_A_D_B_C.
			pose proof (lemma_s_col_BetS_A_B_C C F E BetS_C_F_E) as Col_C_F_E.
			pose proof (lemma_collinearorder _ _ _ Col_C_F_E) as (_ & _ & _ & _ & Col_E_F_C).
			pose proof (lemma_betweennotequal _ _ _ BetS_A_B_E) as (neq_B_E & _ & _).
			pose proof (lemma_s_col_BetS_A_B_C A B E BetS_A_B_E) as Col_A_B_E.
			pose proof (lemma_collinearorder _ _ _ Col_A_B_E) as (_ & _ & _ & _ & Col_E_B_A).
			assert (Col E B C) as Col_E_B_C by (rewrite eq_B_F; exact Col_E_F_C).
			pose proof (lemma_inequalitysymmetric _ _ neq_B_E) as neq_E_B.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_B_A Col_E_B_C neq_E_B) as Col_B_A_C.
			pose proof (lemma_collinearorder _ _ _ Col_B_A_C) as (_ & Col_A_C_B & _ & _ & _).
			contradict Col_A_C_B.
			exact n_Col_A_C_B.
		}
		assert (Cross_A_D_B_C := n_n_Cross_A_D_B_C).
		apply Classical_Prop.NNPP in Cross_A_D_B_C.

		exact Cross_A_D_B_C.
	}
	{
		(* case eq_D_F *)
		assert (nCol A C F) as nCol_A_C_F by (rewrite <- eq_D_F; exact nCol_A_C_D).
		pose proof (lemma_NCorder _ _ _ nCol_A_C_F) as (_ & nCol_C_F_A & _ & _ & _).
		pose proof (lemma_s_col_BetS_A_B_C C F E BetS_C_F_E) as Col_C_F_E.
		assert (eq C C) as eq_C_C by (reflexivity).
		pose proof (lemma_s_col_eq_A_C C F C eq_C_C) as Col_C_F_C.
		pose proof (lemma_betweennotequal _ _ _ BetS_C_F_E) as (_ & _ & neq_C_E).
		pose proof (lemma_NChelper _ _ _ _ _ nCol_C_F_A Col_C_F_C Col_C_F_E neq_C_E) as nCol_C_E_A.
		pose proof (lemma_NCorder _ _ _ nCol_C_E_A) as (_ & _ & _ & _ & nCol_A_E_C).
		pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_A_B_E BetS_C_F_E nCol_A_E_C) as (M & BetS_A_M_F & BetS_C_M_B).
		assert (BetS A M D) as BetS_A_M_D by (rewrite eq_D_F; exact BetS_A_M_F).
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_M_B) as BetS_B_M_C.

		unfold Cross.
		exists M.
		split.
		exact BetS_A_M_D.
		exact BetS_B_M_C.
	}
	{
		(* case BetS_D_B_F *)

		assert (~ ~ Cross A D B C) as n_n_Cross_A_D_B_C.
		{
			intro n_Cross_A_D_B_C.
			pose proof (lemma_NCorder _ _ _ nCol_B_D_C) as (nCol_D_B_C & _ & _ & _ & _).
			assert (eq D D) as eq_D_D by (reflexivity).
			pose proof (lemma_s_col_eq_A_C D B D eq_D_D) as Col_D_B_D.
			pose proof (lemma_collinearorder _ _ _ Col_B_D_F) as (Col_D_B_F & _ & _ & _ & _).
			pose proof (lemma_betweennotequal _ _ _ BetS_D_B_F) as (_ & _ & neq_D_F).
			pose proof (lemma_NChelper _ _ _ _ _ nCol_D_B_C Col_D_B_D Col_D_B_F neq_D_F) as nCol_D_F_C.
			pose proof (lemma_NCorder _ _ _ nCol_D_F_C) as (_ & _ & _ & _ & nCol_C_F_D).
			pose proof (lemma_s_col_BetS_A_B_C C F E BetS_C_F_E) as Col_C_F_E.
			assert (eq C C) as eq_C_C by (reflexivity).
			pose proof (lemma_s_col_eq_A_C C F C eq_C_C) as Col_C_F_C.
			pose proof (lemma_betweennotequal _ _ _ BetS_C_F_E) as (_ & _ & neq_C_E).
			pose proof (lemma_NChelper _ _ _ _ _ nCol_C_F_D Col_C_F_C Col_C_F_E neq_C_E) as nCol_C_E_D.
			pose proof (lemma_NCorder _ _ _ nCol_C_E_D) as (nCol_E_C_D & _ & _ & _ & _).
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_F_E) as BetS_E_F_C.
			pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_D_B_F BetS_E_F_C nCol_E_C_D) as (M & BetS_D_M_C & BetS_E_B_M).
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_M_C) as BetS_C_M_D.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_B_M) as BetS_M_B_E.
			pose proof (lemma_s_col_BetS_A_B_C A B E BetS_A_B_E) as Col_A_B_E.
			pose proof (lemma_s_col_BetS_A_B_C E B M BetS_E_B_M) as Col_E_B_M.
			pose proof (lemma_collinearorder _ _ _ Col_A_B_E) as (_ & _ & _ & _ & Col_E_B_A).
			pose proof (lemma_betweennotequal _ _ _ BetS_A_B_E) as (neq_B_E & _ & _).
			pose proof (lemma_inequalitysymmetric _ _ neq_B_E) as neq_E_B.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_B_M Col_E_B_A neq_E_B) as Col_B_M_A.
			pose proof (lemma_collinearorder _ _ _ Col_B_M_A) as (_ & _ & Col_A_B_M & _ & _).
			pose proof (lemma_parallelflip _ _ _ _ Par_A_C_B_D) as (Par_C_A_B_D & _ & _).

			destruct Par_C_A_B_D as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _ & _ & _ & _ & _ & _ & _ & n_Meet_C_A_B_D & _ & _).

			assert (eq A A) as eq_A_A by (reflexivity).
			pose proof (lemma_s_col_eq_B_C C A A eq_A_A) as Col_C_A_A.
			pose proof (lemma_s_col_eq_A_B B B D eq_B_B) as Col_B_B_D.
			pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_C_A_A Col_B_B_D neq_C_A neq_B_D neq_C_A neq_B_D n_Meet_C_A_B_D BetS_C_M_D Col_A_B_M) as BetS_A_M_B.

			assert (Cross A B C D) as Cross_A_B_C_D.
			unfold Cross.
			exists M.
			split.
			exact BetS_A_M_B.
			exact BetS_C_M_D.

			contradict Cross_A_B_C_D.
			exact n_Cross_A_B_C_D.
		}
		assert (Cross_A_D_B_C := n_n_Cross_A_D_B_C).
		apply Classical_Prop.NNPP in Cross_A_D_B_C.


		exact Cross_A_D_B_C.
	}
	{
		(* case BetS_B_D_F *)
		assert (eq A A) as eq_A_A by (reflexivity).
		pose proof (lemma_s_col_eq_A_C A B A eq_A_A) as Col_A_B_A.
		pose proof (lemma_s_col_BetS_A_B_C A B E BetS_A_B_E) as Col_A_B_E.
		pose proof (lemma_betweennotequal _ _ _ BetS_A_B_E) as (_ & _ & neq_A_E).
		pose proof (lemma_NCorder _ _ _ nCol_A_C_B) as (_ & _ & _ & nCol_A_B_C & _).
		pose proof (lemma_NChelper _ _ _ _ _ nCol_A_B_C Col_A_B_A Col_A_B_E neq_A_E) as nCol_A_E_C.
		pose proof (lemma_collinearorder _ _ _ Col_A_B_E) as (_ & _ & _ & Col_A_E_B & _).
		assert (eq E E) as eq_E_E by (reflexivity).
		pose proof (lemma_s_col_eq_B_C A E E eq_E_E) as Col_A_E_E.
		pose proof (lemma_betweennotequal _ _ _ BetS_A_B_E) as (neq_B_E & _ & _).
		pose proof (lemma_NChelper _ _ _ _ _ nCol_A_E_C Col_A_E_B Col_A_E_E neq_B_E) as nCol_B_E_C.
		pose proof (lemma_NCorder _ _ _ nCol_B_E_C) as (_ & _ & _ & _ & nCol_C_E_B).
		pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_B_D_F BetS_C_F_E nCol_C_E_B) as (J & BetS_B_J_E & BetS_C_D_J).
		pose proof (lemma_orderofpoints_ABD_BCD_ACD _ _ _ _ BetS_A_B_E BetS_B_J_E) as BetS_A_J_E.
		pose proof (lemma_s_col_BetS_A_B_C A J E BetS_A_J_E) as Col_A_J_E.
		pose proof (lemma_collinearorder _ _ _ Col_A_E_B) as (Col_E_A_B & _ & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_A_J_E) as (_ & _ & Col_E_A_J & _ & _).
		pose proof (lemma_inequalitysymmetric _ _ neq_A_E) as neq_E_A.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_A_B Col_E_A_J neq_E_A) as Col_A_B_J.
		pose proof (lemma_betweennotequal _ _ _ BetS_A_J_E) as (_ & neq_A_J & _).
		pose proof (lemma_NChelper _ _ _ _ _ nCol_A_B_C Col_A_B_A Col_A_B_J neq_A_J) as nCol_A_J_C.
		pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_A_B_E BetS_B_J_E) as BetS_A_B_J.
		pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_A_B_J BetS_C_D_J nCol_A_J_C) as (M & BetS_A_M_D & BetS_C_M_B).
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_M_B) as BetS_B_M_C.

		assert (Cross A D B C) as Cross_A_D_B_C.
		unfold Cross.
		exists M.
		split.
		exact BetS_A_M_D.
		exact BetS_B_M_C.

		exact Cross_A_D_B_C.
	}
	{
		(* case BetS_B_F_D *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_F_D) as BetS_D_F_B.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_E) as BetS_E_B_A.
		pose proof (lemma_s_col_BetS_A_B_C A B E BetS_A_B_E) as Col_A_B_E.
		assert (eq A A) as eq_A_A by (reflexivity).
		pose proof (lemma_s_col_eq_A_C A B A eq_A_A) as Col_A_B_A.
		pose proof (lemma_betweennotequal _ _ _ BetS_A_B_E) as (_ & _ & neq_A_E).
		pose proof (lemma_NChelper _ _ _ _ _ nCol_A_B_D Col_A_B_A Col_A_B_E neq_A_E) as nCol_A_E_D.
		pose proof (lemma_NCorder _ _ _ nCol_A_E_D) as (nCol_E_A_D & _ & _ & _ & _).
		pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_D_F_B BetS_E_B_A nCol_E_A_D) as (Q & BetS_D_Q_A & BetS_E_F_Q).
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_F_E) as BetS_E_F_C.
		pose proof (lemma_s_col_BetS_A_B_C E F Q BetS_E_F_Q) as Col_E_F_Q.
		pose proof (lemma_s_col_BetS_A_B_C E F C BetS_E_F_C) as Col_E_F_C.
		pose proof (lemma_betweennotequal _ _ _ BetS_C_F_E) as (neq_F_E & _ & _).
		pose proof (lemma_inequalitysymmetric _ _ neq_F_E) as neq_E_F.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_F_Q Col_E_F_C neq_E_F) as Col_F_Q_C.
		pose proof (lemma_collinearorder _ _ _ Col_F_Q_C) as (_ & _ & _ & Col_F_C_Q & _).
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_Q_A) as BetS_A_Q_D.
		pose proof (lemma_s_col_BetS_A_B_C B F D BetS_B_F_D) as Col_B_F_D.
		pose proof (lemma_betweennotequal _ _ _ BetS_B_F_D) as (neq_F_D & _ & _).
		pose proof (lemma_collinearparallel _ _ _ _ _ Par_A_C_B_D Col_B_D_F neq_F_D) as Par_A_C_F_D.
		destruct Par_A_C_F_D as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _ & _ & _ & _ & _ & _ & _ & n_Meet_A_C_F_D & _ & _).
		assert (eq C C) as eq_C_C by (reflexivity).
		assert (eq F F) as eq_F_F by (reflexivity).
		pose proof (lemma_s_col_eq_B_C A C C eq_C_C) as Col_A_C_C.
		pose proof (lemma_s_col_eq_A_B F F D eq_F_F) as Col_F_F_D.
		pose proof (lemma_collinearorder _ _ _ Col_F_C_Q) as (Col_C_F_Q & _ & _ & _ & _).
		pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_A_C_C Col_F_F_D neq_A_C neq_F_D neq_A_C neq_F_D n_Meet_A_C_F_D BetS_A_Q_D Col_C_F_Q) as BetS_C_Q_F.
		pose proof (lemma_NCorder _ _ _ nCol_A_C_B) as (_ & _ & _ & nCol_A_B_C & _).
		pose proof (lemma_NChelper _ _ _ _ _ nCol_A_B_C Col_A_B_A Col_A_B_E neq_A_E) as nCol_A_E_C.
		pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_C_Q_F BetS_C_F_E) as BetS_C_Q_E.
		pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_A_B_E BetS_C_Q_E nCol_A_E_C) as (M & BetS_A_M_Q & BetS_C_M_B).
		pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_A_M_Q BetS_A_Q_D) as BetS_A_M_D.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_M_B) as BetS_B_M_C.

		assert (Cross A D B C) as Cross_A_D_B_C.
		unfold Cross.
		exists M.
		split.
		exact BetS_A_M_D.
		exact BetS_B_M_C.

		exact Cross_A_D_B_C.
	}

	exact Cross_A_D_B_C.
Qed.

End Euclid.
