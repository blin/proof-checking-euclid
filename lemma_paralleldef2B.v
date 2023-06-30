Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_parallelcollinear.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_meet.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_par.
Require Import ProofCheckingEuclid.lemma_s_ss.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_tarskiparallelflip.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_paralleldef2B :
	forall A B C D,
	Par A B C D ->
	TP A B C D.
Proof.
	intros A B C D.
	intros Par_A_B_C_D.


	destruct Par_A_B_C_D as (a & b & c & d & e & neq_A_B & neq_C_D & Col_A_B_a & Col_A_B_b & neq_a_b & Col_C_D_c & Col_C_D_d & neq_c_d & n_Meet_A_B_C_D & BetS_a_e_d & BetS_c_e_b).

	pose proof (lemma_inequalitysymmetric _ _ neq_a_b) as neq_b_a.
	pose proof (lemma_betweennotequal _ _ _ BetS_c_e_b) as (neq_e_b & _ & _).

	assert (~ Meet a b C D) as n_Meet_a_b_C_D.
	{
		intro Meet_a_b_C_D.

		destruct Meet_a_b_C_D as (R & _ & _ & Col_a_b_R & Col_C_D_R).
		pose proof (lemma_collinearorder _ _ _ Col_a_b_R) as (Col_b_a_R & _ & _ & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_a Col_A_B_b neq_A_B) as Col_B_a_b.
		pose proof (lemma_collinearorder _ _ _ Col_B_a_b) as (_ & _ & _ & _ & Col_b_a_B).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_b_a_B Col_b_a_R neq_b_a) as Col_a_B_R.
		pose proof (lemma_collinearorder _ _ _ Col_A_B_a) as (_ & _ & _ & _ & Col_a_B_A).

		(* assert by cases *)
		assert (Col A B R) as Col_A_B_R.
		assert (eq a B \/ neq a B) as [eq_a_B|neq_a_B] by (apply Classical_Prop.classic).
		{
			(* case eq_a_B *)
			assert (neq A a) as neq_A_a by (rewrite eq_a_B; exact neq_A_B).
			pose proof (lemma_collinearorder _ _ _ Col_A_B_a) as (Col_B_A_a & _ & _ & _ & _).
			pose proof (lemma_collinearorder _ _ _ Col_A_B_b) as (Col_B_A_b & _ & _ & _ & _).
			pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_a Col_B_A_b neq_B_A) as Col_A_a_b.
			pose proof (lemma_collinearorder _ _ _ Col_A_a_b) as (_ & _ & _ & _ & Col_b_a_A).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_b_a_A Col_b_a_R neq_b_a) as Col_a_A_R.
			pose proof (lemma_collinearorder _ _ _ Col_A_B_a) as (_ & _ & Col_a_A_B & _ & _).
			pose proof (lemma_inequalitysymmetric _ _ neq_A_a) as neq_a_A.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_a_A_R Col_a_A_B neq_a_A) as Col_A_R_B.
			pose proof (lemma_collinearorder _ _ _ Col_A_R_B) as (_ & _ & _ & Col_A_B_R & _).

			exact Col_A_B_R.
		}
		{
			(* case neq_a_B *)
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_a_B_R Col_a_B_A neq_a_B) as Col_B_R_A.
			pose proof (lemma_collinearorder _ _ _ Col_B_R_A) as (_ & _ & Col_A_B_R & _ & _).

			exact Col_A_B_R.
		}
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_R Col_C_D_R) as Meet_A_B_C_D.
		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	pose proof (lemma_extension e b e b neq_e_b neq_e_b) as (P & BetS_e_b_P & Cong_b_P_e_b).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_e_b_P) as BetS_P_b_e.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_e_b) as BetS_b_e_c.
	pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_P_b_e BetS_b_e_c) as BetS_P_b_c.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_b_c) as BetS_c_b_P.

	assert (~ Col a d P) as n_Col_a_d_P.
	{
		intro Col_a_d_P.
		pose proof (lemma_s_col_BetS_A_B_C a e d BetS_a_e_d) as Col_a_e_d.
		pose proof (lemma_collinearorder _ _ _ Col_a_e_d) as (_ & _ & _ & Col_a_d_e & _).
		pose proof (lemma_betweennotequal _ _ _ BetS_a_e_d) as (_ & _ & neq_a_d).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_a_d_P Col_a_d_e neq_a_d) as Col_d_P_e.
		pose proof (lemma_collinearorder _ _ _ Col_d_P_e) as (_ & _ & _ & _ & Col_e_P_d).
		pose proof (lemma_s_col_BetS_A_B_C e b P BetS_e_b_P) as Col_e_b_P.
		pose proof (lemma_collinearorder _ _ _ Col_e_b_P) as (_ & _ & _ & Col_e_P_b & _).
		pose proof (lemma_betweennotequal _ _ _ BetS_e_b_P) as (_ & _ & neq_e_P).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_e_P_d Col_e_P_b neq_e_P) as Col_P_d_b.
		pose proof (lemma_collinearorder _ _ _ Col_P_d_b) as (Col_d_P_b & _ & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_a_d_P) as (_ & Col_d_P_a & _ & _ & _).

		assert (~ eq d P) as n_eq_d_P.
		{
			intro eq_d_P.
			pose proof (lemma_s_col_BetS_A_B_C c b P BetS_c_b_P) as Col_c_b_P.
			assert (Col c b d) as Col_c_b_d by (rewrite eq_d_P; exact Col_c_b_P).
			pose proof (lemma_s_col_BetS_A_B_C b e c BetS_b_e_c) as Col_b_e_c.
			pose proof (lemma_collinearorder _ _ _ Col_b_e_c) as (_ & _ & Col_c_b_e & _ & _).
			pose proof (lemma_betweennotequal _ _ _ BetS_c_b_P) as (_ & neq_c_b & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_c_b_d Col_c_b_e neq_c_b) as Col_b_d_e.
			pose proof (lemma_collinearorder _ _ _ Col_a_d_e) as (_ & Col_d_e_a & _ & _ & _).
			pose proof (lemma_collinearorder _ _ _ Col_b_d_e) as (_ & Col_d_e_b & _ & _ & _).
			pose proof (lemma_betweennotequal _ _ _ BetS_a_e_d) as (neq_e_d & _ & _).
			pose proof (lemma_inequalitysymmetric _ _ neq_e_d) as neq_d_e.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_d_e_a Col_d_e_b neq_d_e) as Col_e_a_b.
			pose proof (lemma_collinearorder _ _ _ Col_a_e_d) as (Col_e_a_d & _ & _ & _ & _).
			pose proof (lemma_betweennotequal _ _ _ BetS_a_e_d) as (_ & neq_a_e & _).
			pose proof (lemma_inequalitysymmetric _ _ neq_a_e) as neq_e_a.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_e_a_b Col_e_a_d neq_e_a) as Col_a_b_d.
			pose proof (lemma_s_meet _ _ _ _ _ neq_a_b neq_C_D Col_a_b_d Col_C_D_d) as Meet_a_b_C_D.
			contradict Meet_a_b_C_D.
			exact n_Meet_a_b_C_D.
		}
		assert (neq_d_P := n_eq_d_P).


		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_d_P_b Col_d_P_a neq_d_P) as Col_P_b_a.
		pose proof (lemma_s_col_BetS_A_B_C P b c BetS_P_b_c) as Col_P_b_c.
		pose proof (lemma_betweennotequal _ _ _ BetS_e_b_P) as (neq_b_P & _ & _).
		pose proof (lemma_inequalitysymmetric _ _ neq_b_P) as neq_P_b.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_P_b_a Col_P_b_c neq_P_b) as Col_b_a_c.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_a Col_A_B_b neq_A_B) as Col_B_a_b.
		pose proof (lemma_collinearorder _ _ _ Col_B_a_b) as (_ & _ & _ & _ & Col_b_a_B).
		pose proof (lemma_collinearorder _ _ _ Col_b_a_c) as (Col_a_b_c & _ & _ & _ & _).
		assert (eq c c) as eq_c_c by (reflexivity).
		pose proof (lemma_s_meet _ _ _ _ _ neq_a_b neq_C_D Col_a_b_c Col_C_D_c) as Meet_a_b_C_D.
		contradict Meet_a_b_C_D.
		exact n_Meet_a_b_C_D.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_a_d_P) as nCol_a_d_P.

	pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_P_b_e BetS_a_e_d nCol_a_d_P) as (M & BetS_P_M_d & BetS_a_b_M).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_a_b_M) as BetS_M_b_a.
	pose proof (lemma_s_col_BetS_A_B_C a b M BetS_a_b_M) as Col_a_b_M.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_a Col_A_B_b neq_A_B) as Col_B_a_b.
	pose proof (lemma_collinearorder _ _ _ Col_B_a_b) as (_ & _ & _ & _ & Col_b_a_B).
	pose proof (lemma_collinearorder _ _ _ Col_a_b_M) as (Col_b_a_M & _ & _ & _ & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_b_a_B Col_b_a_M neq_b_a) as Col_a_B_M.
	pose proof (lemma_collinearorder _ _ _ Col_A_B_a) as (_ & _ & _ & _ & Col_a_B_A).

	(* assert by cases *)
	assert (Col A B M) as Col_A_B_M.
	assert (eq a B \/ neq a B) as [eq_a_B|neq_a_B] by (apply Classical_Prop.classic).
	{
		(* case eq_a_B *)
		assert (neq A a) as neq_A_a by (rewrite eq_a_B; exact neq_A_B).
		assert (Col A a b) as Col_A_a_b by (rewrite eq_a_B; exact Col_A_B_b).
		pose proof (lemma_collinearorder _ _ _ Col_A_a_b) as (_ & _ & _ & _ & Col_b_a_A).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_b_a_A Col_b_a_M neq_b_a) as Col_a_A_M.
		pose proof (lemma_collinearorder _ _ _ Col_A_B_a) as (_ & _ & Col_a_A_B & _ & _).
		pose proof (lemma_inequalitysymmetric _ _ neq_A_a) as neq_a_A.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_a_A_M Col_a_A_B neq_a_A) as Col_A_M_B.
		pose proof (lemma_collinearorder _ _ _ Col_A_M_B) as (_ & _ & _ & Col_A_B_M & _).

		exact Col_A_B_M.
	}
	{
		(* case neq_a_B *)
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_a_B_M Col_a_B_A neq_a_B) as Col_B_M_A.
		pose proof (lemma_collinearorder _ _ _ Col_B_M_A) as (_ & _ & Col_A_B_M & _ & _).

		exact Col_A_B_M.
	}
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_M_d) as BetS_d_M_P.

	assert (~ Col A B c) as n_Col_A_B_c.
	{
		intro Col_A_B_c.
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_c Col_C_D_c) as Meet_A_B_C_D.
		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_B_c) as nCol_A_B_c.


	assert (~ Col A B d) as n_Col_A_B_d.
	{
		intro Col_A_B_d.
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_d Col_C_D_d) as Meet_A_B_C_D.
		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_B_d) as nCol_A_B_d.

	pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_A_B_b Col_A_B_M BetS_c_b_P BetS_d_M_P nCol_A_B_c nCol_A_B_d) as SS_c_d_A_B.

	assert (~ Meet A B c d) as n_Meet_A_B_c_d.
	{
		intro Meet_A_B_c_d.

		destruct Meet_A_B_c_d as (R & _ & _ & Col_A_B_R & Col_c_d_R).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_D_c Col_C_D_d neq_C_D) as Col_D_c_d.
		pose proof (lemma_collinearorder _ _ _ Col_C_D_c) as (Col_D_C_c & _ & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_C_D_d) as (Col_D_C_d & _ & _ & _ & _).
		pose proof (lemma_inequalitysymmetric _ _ neq_C_D) as neq_D_C.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_C_c Col_D_C_d neq_D_C) as Col_C_c_d.
		pose proof (lemma_collinearorder _ _ _ Col_C_c_d) as (_ & Col_c_d_C & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_D_c_d) as (_ & Col_c_d_D & _ & _ & _).
		pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_c_d Col_c_d_C Col_c_d_D Col_c_d_R) as Col_C_D_R.
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_R Col_C_D_R) as Meet_A_B_C_D.
		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	assert (TP A B c d) as TP_A_B_c_d.
	unfold TP.
	split.
	exact neq_A_B.
	split.
	exact neq_c_d.
	split.
	exact n_Meet_A_B_c_d.
	exact SS_c_d_A_B.

	assert (eq C C) as eq_C_C by (reflexivity).
	pose proof (lemma_s_col_eq_A_C C D C eq_C_C) as Col_C_D_C.
	pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_C_D Col_C_D_c Col_C_D_d Col_C_D_C) as Col_c_d_C.

	assert (~ ~ TP A B C D) as n_n_TP_A_B_C_D.
	{
		intro n_TP_A_B_C_D.
		pose proof (lemma_inequalitysymmetric _ _ neq_C_D) as neq_D_C.

		assert (~ neq C d) as n_neq_C_d.
		{
			intro neq_C_d.
			pose proof (lemma_parallelcollinear _ _ _ _ _ TP_A_B_c_d Col_c_d_C neq_C_d) as TP_A_B_C_d.
			pose proof (lemma_tarskiparallelflip _ _ _ _ TP_A_B_C_d) as (_ & TP_A_B_d_C & _).
			pose proof (lemma_collinearorder _ _ _ Col_C_D_d) as (_ & _ & Col_d_C_D & _ & _).
			pose proof (lemma_parallelcollinear _ _ _ _ _ TP_A_B_d_C Col_d_C_D neq_D_C) as TP_A_B_D_C.
			pose proof (lemma_tarskiparallelflip _ _ _ _ TP_A_B_D_C) as (_ & TP_A_B_C_D & _).
			contradict TP_A_B_C_D.
			exact n_TP_A_B_C_D.
		}
		assert (eq_C_d := n_neq_C_d).
		apply Classical_Prop.NNPP in eq_C_d.


		assert (TP A B c C) as TP_A_B_c_C by (rewrite eq_C_d; exact TP_A_B_c_d).
		pose proof (lemma_collinearorder _ _ _ Col_C_D_c) as (_ & _ & Col_c_C_D & _ & _).
		pose proof (lemma_parallelcollinear _ _ _ _ _ TP_A_B_c_C Col_c_C_D neq_D_C) as TP_A_B_D_C.
		pose proof (lemma_tarskiparallelflip _ _ _ _ TP_A_B_D_C) as (_ & TP_A_B_C_D & _).
		contradict TP_A_B_C_D.
		exact n_TP_A_B_C_D.
	}
	assert (TP_A_B_C_D := n_n_TP_A_B_C_D).
	apply Classical_Prop.NNPP in TP_A_B_C_D.

	exact TP_A_B_C_D.
Qed.

End Euclid.

