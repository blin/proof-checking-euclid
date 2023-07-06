Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NChelper.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
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
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_ss.
Require Import ProofCheckingEuclid.lemma_s_triangle.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_tarski_parallel_collinear_ABcd_Ccd_ABCd :
	forall A B C c d,
	TP A B c d ->
	BetS C c d ->
	TP A B C d.
Proof.
	intros A B C c d.
	intros TP_A_B_c_d.
	intros BetS_C_c_d.

	pose proof (lemma_s_col_BetS_A_B_C C c d BetS_C_c_d) as Col_C_c_d.
	pose proof (lemma_betweennotequal _ _ _ BetS_C_c_d) as (_ & neq_C_c & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_C_c_d) as (neq_c_d & _ & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_C_c_d) as (_ & _ & neq_C_d).

	destruct TP_A_B_c_d as (neq_A_B & _ & n_Meet_A_B_c_d & SS_c_d_A_B).

	destruct SS_c_d_A_B as (q & p & r & Col_A_B_p & Col_A_B_r & BetS_c_p_q & BetS_d_r_q & nCol_A_B_c & nCol_A_B_d).

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_d) as n_Col_A_B_d.


	pose proof (axiom_betweennesssymmetry _ _ _ BetS_d_r_q) as BetS_q_r_d.
	pose proof (lemma_collinearorder _ _ _ Col_C_c_d) as (_ & Col_c_d_C & _ & _ & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_c_d) as BetS_d_c_C.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_p_q) as BetS_q_p_c.

	assert (~ eq p r) as n_eq_p_r.
	{
		intro eq_p_r.
		pose proof (lemma_s_col_BetS_A_B_C q r d BetS_q_r_d) as Col_q_r_d.
		pose proof (lemma_s_col_BetS_A_B_C q p c BetS_q_p_c) as Col_q_p_c.
		assert (Col q p d) as Col_q_p_d by (rewrite eq_p_r; exact Col_q_r_d).
		pose proof (lemma_betweennotequal _ _ _ BetS_q_p_c) as (_ & neq_q_p & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_q_p_c Col_q_p_d neq_q_p) as Col_p_c_d.
		pose proof (lemma_collinearorder _ _ _ Col_p_c_d) as (_ & Col_c_d_p & _ & _ & _).
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_c_d Col_A_B_p Col_c_d_p) as Meet_A_B_c_d.
		contradict Meet_A_B_c_d.
		exact n_Meet_A_B_c_d.
	}
	assert (neq_p_r := n_eq_p_r).


	pose proof (lemma_s_col_BetS_A_B_C q p c BetS_q_p_c) as Col_q_p_c.

	assert (~ Col q d C) as n_Col_q_d_C.
	{
		intro Col_q_d_C.
		pose proof (lemma_s_col_BetS_A_B_C d c C BetS_d_c_C) as Col_d_c_C.
		pose proof (lemma_collinearorder _ _ _ Col_d_c_C) as (_ & _ & Col_C_d_c & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_q_d_C) as (_ & _ & _ & _ & Col_C_d_q).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_d_c Col_C_d_q neq_C_d) as Col_d_c_q.
		pose proof (lemma_collinearorder _ _ _ Col_d_c_q) as (_ & Col_c_q_d & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_q_p_c) as (_ & _ & Col_c_q_p & _ & _).
		pose proof (lemma_betweennotequal _ _ _ BetS_q_p_c) as (_ & _ & neq_q_c).
		pose proof (lemma_inequalitysymmetric _ _ neq_q_c) as neq_c_q.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_c_q_d Col_c_q_p neq_c_q) as Col_q_d_p.
		pose proof (lemma_s_col_BetS_A_B_C q r d BetS_q_r_d) as Col_q_r_d.
		pose proof (lemma_collinearorder _ _ _ Col_q_r_d) as (_ & _ & _ & Col_q_d_r & _).
		pose proof (lemma_betweennotequal _ _ _ BetS_q_r_d) as (_ & _ & neq_q_d).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_q_d_p Col_q_d_r neq_q_d) as Col_d_p_r.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_p Col_A_B_r neq_A_B) as Col_B_p_r.
		pose proof (lemma_collinearorder _ _ _ Col_A_B_p) as (Col_B_A_p & _ & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_A_B_p) as (_ & Col_B_p_A & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_A_B_r) as (Col_B_A_r & _ & _ & _ & _).
		pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_p Col_B_A_r neq_B_A) as Col_A_p_r.

		assert (~ neq B p) as n_neq_B_p.
		{
			intro neq_B_p.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_p_r Col_B_p_A neq_B_p) as Col_p_r_A.
			pose proof (lemma_collinearorder _ _ _ Col_d_p_r) as (_ & Col_p_r_d & _ & _ & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_p_r_A Col_p_r_d neq_p_r) as Col_r_A_d.
			pose proof (lemma_collinearorder _ _ _ Col_A_B_r) as (_ & _ & Col_r_A_B & _ & _).

			assert (~ neq r A) as n_neq_r_A.
			{
				intro neq_r_A.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_r_A_d Col_r_A_B neq_r_A) as Col_A_d_B.
				pose proof (lemma_collinearorder _ _ _ Col_A_d_B) as (_ & _ & _ & Col_A_B_d & _).
				contradict Col_A_B_d.
				exact n_Col_A_B_d.
			}
			assert (eq_r_A := n_neq_r_A).
			apply Classical_Prop.NNPP in eq_r_A.


			assert (Col p A d) as Col_p_A_d by (rewrite <- eq_r_A; exact Col_p_r_d).
			pose proof (lemma_collinearorder _ _ _ Col_B_p_A) as (_ & Col_p_A_B & _ & _ & _).

			assert (~ neq p A) as n_neq_p_A.
			{
				intro neq_p_A.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_p_A_d Col_p_A_B neq_p_A) as Col_A_d_B.
				pose proof (lemma_collinearorder _ _ _ Col_A_d_B) as (_ & _ & _ & Col_A_B_d & _).
				contradict Col_A_B_d.
				exact n_Col_A_B_d.
			}
			assert (eq_p_A := n_neq_p_A).
			apply Classical_Prop.NNPP in eq_p_A.


			pose proof (lemma_equalitysymmetric _ _ eq_p_A) as eq_A_p.
			assert (eq r p) as eq_r_p by (rewrite eq_p_A; exact eq_r_A).
			assert (Col q p d) as Col_q_p_d by (rewrite <- eq_r_p; exact Col_q_r_d).
			pose proof (lemma_betweennotequal _ _ _ BetS_q_p_c) as (_ & neq_q_p & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_q_p_c Col_q_p_d neq_q_p) as Col_p_c_d.
			pose proof (lemma_collinearorder _ _ _ Col_p_c_d) as (_ & Col_c_d_p & _ & _ & _).
			pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_c_d Col_A_B_p Col_c_d_p) as Meet_A_B_c_d.
			contradict Meet_A_B_c_d.
			exact n_Meet_A_B_c_d.
		}
		assert (eq_B_p := n_neq_B_p).
		apply Classical_Prop.NNPP in eq_B_p.


		assert (neq A p) as neq_A_p by (rewrite <- eq_B_p; exact neq_A_B).
		pose proof (lemma_collinearorder _ _ _ Col_B_A_p) as (_ & Col_A_p_B & _ & _ & _).

		assert (~ eq r A) as n_eq_r_A.
		{
			intro eq_r_A.
			assert (Col d p A) as Col_d_p_A by (rewrite <- eq_r_A; exact Col_d_p_r).
			assert (Col d B A) as Col_d_B_A by (rewrite eq_B_p; exact Col_d_p_A).
			pose proof (lemma_collinearorder _ _ _ Col_d_B_A) as (_ & _ & _ & _ & Col_A_B_d).
			contradict Col_A_B_d.
			exact n_Col_A_B_d.
		}
		assert (neq_r_A := n_eq_r_A).


		pose proof (lemma_collinearorder _ _ _ Col_A_B_r) as (_ & _ & Col_r_A_B & _ & _).
		assert (Col d B r) as Col_d_B_r by (rewrite eq_B_p; exact Col_d_p_r).
		pose proof (lemma_collinearorder _ _ _ Col_d_B_r) as (_ & _ & _ & _ & Col_r_B_d).
		pose proof (lemma_collinearorder _ _ _ Col_B_A_r) as (_ & _ & Col_r_B_A & _ & _).

		assert (~ neq r B) as n_neq_r_B.
		{
			intro neq_r_B.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_r_B_d Col_r_B_A neq_r_B) as Col_B_d_A.
			pose proof (lemma_collinearorder _ _ _ Col_B_d_A) as (_ & _ & Col_A_B_d & _ & _).
			contradict Col_A_B_d.
			exact n_Col_A_B_d.
		}
		assert (eq_r_B := n_neq_r_B).
		apply Classical_Prop.NNPP in eq_r_B.


		pose proof (lemma_equalitysymmetric _ _ eq_r_B) as eq_B_r.
		pose proof (lemma_equalitysymmetric _ _ eq_B_p) as eq_p_B.
		assert (eq p r) as eq_p_r by (rewrite eq_r_B; exact eq_p_B).
		contradict eq_p_r.
		exact n_eq_p_r.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_q_d_C) as nCol_q_d_C.

	pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_q_r_d BetS_C_c_d nCol_q_d_C) as (E & BetS_q_E_c & BetS_C_E_r).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_E_r) as BetS_r_E_C.
	pose proof (lemma_s_col_BetS_A_B_C q E c BetS_q_E_c) as Col_q_E_c.
	pose proof (lemma_collinearorder _ _ _ Col_q_p_c) as (_ & _ & _ & Col_q_c_p & _).
	pose proof (lemma_collinearorder _ _ _ Col_q_E_c) as (_ & _ & _ & Col_q_c_E & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_q_p_c) as (_ & _ & neq_q_c).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_q_c_p Col_q_c_E neq_q_c) as Col_c_p_E.
	pose proof (lemma_collinearorder _ _ _ Col_c_p_E) as (_ & _ & _ & Col_c_E_p & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_p_r) as neq_r_p.
	pose proof (lemma_extension r p r p neq_r_p neq_r_p) as (J & BetS_r_p_J & Cong_p_J_r_p).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_r_p_J) as BetS_J_p_r.
	pose proof (lemma_s_col_BetS_A_B_C J p r BetS_J_p_r) as Col_J_p_r.
	pose proof (lemma_betweennotequal _ _ _ BetS_J_p_r) as (_ & _ & neq_J_r).
	pose proof (lemma_betweennotequal _ _ _ BetS_J_p_r) as (_ & neq_J_p & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_p Col_A_B_r neq_A_B) as Col_B_p_r.
	pose proof (lemma_collinearorder _ _ _ Col_A_B_p) as (Col_B_A_p & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_r) as (Col_B_A_r & _ & _ & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_p Col_B_A_r neq_B_A) as Col_A_p_r.
	pose proof (lemma_collinearorder _ _ _ Col_A_p_r) as (_ & Col_p_r_A & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_B_p_r) as (_ & Col_p_r_B & _ & _ & _).

	assert (~ Meet C d J r) as n_Meet_C_d_J_r.
	{
		intro Meet_C_d_J_r.

		destruct Meet_C_d_J_r as (K & _ & _ & Col_C_d_K & Col_J_r_K).
		pose proof (lemma_collinearorder _ _ _ Col_C_c_d) as (_ & _ & _ & Col_C_d_c & _).
		pose proof (lemma_inequalitysymmetric _ _ neq_c_d) as neq_d_c.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_d_c Col_C_d_K neq_C_d) as Col_d_c_K.
		pose proof (lemma_collinearorder _ _ _ Col_d_c_K) as (Col_c_d_K & _ & _ & _ & _).
		pose proof (lemma_s_col_BetS_A_B_C r p J BetS_r_p_J) as Col_r_p_J.
		pose proof (lemma_collinearorder _ _ _ Col_J_p_r) as (_ & _ & Col_r_J_p & _ & _).
		pose proof (lemma_betweennotequal _ _ _ BetS_r_p_J) as (_ & _ & neq_r_J).
		pose proof (lemma_collinearorder _ _ _ Col_J_r_K) as (Col_r_J_K & _ & _ & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_r_J_p Col_r_J_K neq_r_J) as Col_J_p_K.
		pose proof (lemma_betweennotequal _ _ _ BetS_r_p_J) as (neq_p_J & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_J_p_K Col_J_p_r neq_J_p) as Col_p_K_r.
		pose proof (lemma_collinearorder _ _ _ Col_p_K_r) as (_ & _ & _ & Col_p_r_K & _).
		pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_p_r Col_p_r_A Col_p_r_B Col_p_r_K) as Col_A_B_K.
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_c_d Col_A_B_K Col_c_d_K) as Meet_A_B_c_d.
		contradict Meet_A_B_c_d.
		exact n_Meet_A_B_c_d.
	}

	pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_C_c_d Col_J_p_r neq_C_d neq_J_r neq_C_c neq_p_r n_Meet_C_d_J_r BetS_C_E_r Col_c_p_E) as BetS_c_E_p.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_E_p) as BetS_p_E_c.
	pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_q_p_c BetS_p_E_c) as BetS_q_p_E.
	pose proof (lemma_NChelper _ _ _ _ _ nCol_A_B_c Col_A_B_p Col_A_B_r neq_p_r) as nCol_p_r_c.
	pose proof (lemma_NCorder _ _ _ nCol_p_r_c) as (_ & _ & _ & nCol_p_c_r & _).
	pose proof (lemma_collinearorder _ _ _ Col_q_p_c) as (_ & Col_p_c_q & _ & _ & _).
	assert (eq c c) as eq_c_c by (reflexivity).
	pose proof (lemma_s_col_eq_B_C p c c eq_c_c) as Col_p_c_c.
	pose proof (lemma_NChelper _ _ _ _ _ nCol_p_c_r Col_p_c_q Col_p_c_c neq_q_c) as nCol_q_c_r.
	pose proof (lemma_NCorder _ _ _ nCol_q_c_r) as (_ & _ & _ & nCol_q_r_c & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_q_r_d) as (_ & _ & neq_q_d).
	pose proof (lemma_s_col_BetS_A_B_C q r d BetS_q_r_d) as Col_q_r_d.
	assert (eq q q) as eq_q_q by (reflexivity).
	pose proof (lemma_s_col_eq_A_C q r q eq_q_q) as Col_q_r_q.
	pose proof (lemma_NChelper _ _ _ _ _ nCol_q_r_c Col_q_r_q Col_q_r_d neq_q_d) as nCol_q_d_c.
	pose proof (lemma_NCorder _ _ _ nCol_q_d_c) as (_ & nCol_d_c_q & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_c_d_C) as (Col_d_c_C & _ & _ & _ & _).
	assert (eq d d) as eq_d_d by (reflexivity).
	pose proof (lemma_s_col_eq_A_C d c d eq_d_d) as Col_d_c_d.
	pose proof (lemma_inequalitysymmetric _ _ neq_C_d) as neq_d_C.
	pose proof (lemma_NChelper _ _ _ _ _ nCol_d_c_q Col_d_c_d Col_d_c_C neq_d_C) as nCol_d_C_q.
	pose proof (lemma_NCorder _ _ _ nCol_q_d_C) as (nCol_d_q_C & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_q_r_d) as (_ & _ & Col_d_q_r & _ & _).
	pose proof (lemma_s_col_eq_B_C d q q eq_q_q) as Col_d_q_q.

	assert (~ eq r C) as n_eq_r_C.
	{
		intro eq_r_C.
		assert (Col A B C) as Col_A_B_C by (rewrite <- eq_r_C; exact Col_A_B_r).
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_c_d Col_A_B_C Col_c_d_C) as Meet_A_B_c_d.
		contradict Meet_A_B_c_d.
		exact n_Meet_A_B_c_d.
	}
	assert (neq_r_C := n_eq_r_C).


	pose proof (lemma_s_ncol_n_col _ _ _ nCol_q_r_c) as n_Col_q_r_c.


	assert (~ eq r q) as n_eq_r_q.
	{
		intro eq_r_q.
		pose proof (lemma_s_col_eq_A_B r q c eq_r_q) as Col_r_q_c.
		pose proof (lemma_collinearorder _ _ _ Col_r_q_c) as (Col_q_r_c & _ & _ & _ & _).
		contradict Col_q_r_c.
		exact n_Col_q_r_c.
	}
	assert (neq_r_q := n_eq_r_q).


	pose proof (lemma_NChelper _ _ _ _ _ nCol_d_q_C Col_d_q_r Col_d_q_q neq_r_q) as nCol_r_q_C.
	pose proof (lemma_NCorder _ _ _ nCol_r_q_C) as (_ & _ & _ & nCol_r_C_q & _).
	pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_q_p_E BetS_r_E_C nCol_r_C_q) as (F & BetS_q_F_C & BetS_r_p_F).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_q_F_C) as BetS_C_F_q.
	pose proof (lemma_s_col_BetS_A_B_C r p F BetS_r_p_F) as Col_r_p_F.
	pose proof (lemma_collinearorder _ _ _ Col_p_r_A) as (Col_r_p_A & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_p_r_B) as (Col_r_p_B & _ & _ & _ & _).
	pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_r_p Col_r_p_A Col_r_p_B Col_r_p_F) as Col_A_B_F.
	assert (eq r r) as eq_r_r by (reflexivity).
	pose proof (lemma_betweennotequal _ _ _ BetS_q_r_d) as (_ & neq_q_r & _).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_d_q_C Col_d_q_q Col_d_q_r neq_q_r) as nCol_q_r_C.
	pose proof (lemma_NCorder _ _ _ nCol_r_q_C) as (_ & nCol_q_C_r & _ & _ & _).
	pose proof (lemma_s_col_BetS_A_B_C q F C BetS_q_F_C) as Col_q_F_C.
	pose proof (lemma_collinearorder _ _ _ Col_q_F_C) as (_ & _ & _ & Col_q_C_F & _).
	assert (eq C C) as eq_C_C by (reflexivity).
	pose proof (lemma_s_col_eq_B_C q C C eq_C_C) as Col_q_C_C.
	pose proof (lemma_betweennotequal _ _ _ BetS_q_F_C) as (neq_F_C & _ & _).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_q_C_r Col_q_C_F Col_q_C_C neq_F_C) as nCol_F_C_r.
	pose proof (lemma_NCorder _ _ _ nCol_F_C_r) as (_ & _ & _ & nCol_F_r_C & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_r Col_A_B_p neq_A_B) as Col_B_r_p.
	pose proof (lemma_collinearorder _ _ _ Col_A_B_p) as (_ & Col_B_p_A & _ & _ & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_r Col_B_A_p neq_B_A) as Col_A_r_p.
	pose proof (lemma_collinearorder _ _ _ Col_r_p_F) as (Col_p_r_F & _ & _ & _ & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_p_r_A Col_p_r_F neq_p_r) as Col_r_A_F.
	pose proof (lemma_collinearorder _ _ _ Col_r_A_F) as (_ & _ & Col_F_r_A & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_B_A_p) as (_ & Col_A_p_B & _ & _ & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_p_r_B Col_p_r_F neq_p_r) as Col_r_B_F.
	pose proof (lemma_collinearorder _ _ _ Col_r_B_F) as (_ & _ & Col_F_r_B & _ & _).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_F_r_C Col_F_r_A Col_F_r_B neq_A_B) as nCol_A_B_C.
	pose proof (lemma_s_os _ _ _ _ _ BetS_C_F_q Col_A_B_F nCol_A_B_C) as OS_C_A_B_q.
	pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_A_B_F Col_A_B_r BetS_C_F_q BetS_d_r_q nCol_A_B_C nCol_A_B_d) as SS_C_d_A_B.

	assert (~ Meet A B C d) as n_Meet_A_B_C_d.
	{
		intro Meet_A_B_C_d.

		destruct Meet_A_B_C_d as (K & _ & _ & Col_A_B_K & Col_C_d_K).
		pose proof (lemma_collinearorder _ _ _ Col_d_c_C) as (_ & _ & Col_C_d_c & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_d_c Col_C_d_K neq_C_d) as Col_d_c_K.
		pose proof (lemma_collinearorder _ _ _ Col_d_c_K) as (Col_c_d_K & _ & _ & _ & _).
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_c_d Col_A_B_K Col_c_d_K) as Meet_A_B_c_d.
		contradict Meet_A_B_c_d.
		exact n_Meet_A_B_c_d.
	}

	unfold TP.
	split.
	exact neq_A_B.
	split.
	exact neq_C_d.
	split.
	exact n_Meet_A_B_C_d.
	exact SS_C_d_A_B.
Qed.

End Euclid.
