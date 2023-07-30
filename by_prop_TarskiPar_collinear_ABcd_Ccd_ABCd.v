Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_SameSide.
Require Import ProofCheckingEuclid.by_def_TarskiPar.
Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_eq_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_TarskiPar_collinear_ABcd_Ccd_ABCd :
	forall A B C c d,
	TarskiPar A B c d ->
	BetS C c d ->
	TarskiPar A B C d.
Proof.
	intros A B C c d.
	intros TarskiPar_AB_cd.
	intros BetS_C_c_d.

	destruct TarskiPar_AB_cd as (neq_A_B & _ & n_Meet_A_B_c_d & SameSide_c_d_AB).

	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.

	destruct SameSide_c_d_AB as (q & p & r & Col_A_B_p & Col_A_B_r & BetS_c_p_q & BetS_d_r_q & nCol_A_B_c & nCol_A_B_d).

	pose proof (by_prop_Col_order _ _ _ Col_A_B_p) as (Col_B_A_p & Col_B_p_A & Col_p_A_B & Col_A_p_B & Col_p_B_A).
	pose proof (by_prop_Col_order _ _ _ Col_A_B_r) as (Col_B_A_r & Col_B_r_A & Col_r_A_B & Col_A_r_B & Col_r_B_A).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_B_p Col_A_B_r neq_A_B) as Col_B_p_r.
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_A_p Col_B_A_r neq_B_A) as Col_A_p_r.
	pose proof (by_prop_Col_order _ _ _ Col_A_p_r) as (Col_p_A_r & Col_p_r_A & Col_r_A_p & Col_A_r_p & Col_r_p_A).
	pose proof (by_prop_Col_order _ _ _ Col_B_p_r) as (_ & Col_p_r_B & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_p_r_B) as (Col_r_p_B & _ & _ & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_p_q) as BetS_q_p_c.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_c_p_q) as (neq_p_q & neq_c_p & neq_c_q).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_q_p_c) as (neq_p_c & neq_q_p & neq_q_c).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_q_p_c) as Col_q_p_c.
	pose proof (by_prop_Col_order _ _ _ Col_q_p_c) as (Col_p_q_c & Col_p_c_q & Col_c_q_p & Col_q_c_p & Col_c_p_q).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_d_r_q) as BetS_q_r_d.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_d_r_q) as (neq_r_q & neq_d_r & neq_d_q).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_q_r_d) as (neq_r_d & neq_q_r & neq_q_d).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_q_r_d) as Col_q_r_d.
	pose proof (by_prop_Col_order _ _ _ Col_q_r_d) as (Col_r_q_d & Col_r_d_q & Col_d_q_r & Col_q_d_r & Col_d_r_q).

	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_d) as n_Col_A_B_d.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_d) as (nCol_B_A_d & nCol_B_d_A & nCol_d_A_B & nCol_A_d_B & nCol_d_B_A).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_c_d) as BetS_d_c_C.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_c_d) as (neq_c_d & neq_C_c & neq_C_d).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_d_c_C) as (neq_c_C & neq_d_c & neq_d_C).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_c_d) as Col_C_c_d.

	pose proof (by_prop_Col_order _ _ _ Col_C_c_d) as (Col_c_C_d & Col_c_d_C & Col_d_C_c & Col_C_d_c & Col_d_c_C).

	assert (~ eq p r) as n_eq_p_r.
	{
		intro eq_p_r.

		assert (Col q p d) as Col_q_p_d by (rewrite eq_p_r; exact Col_q_r_d).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_q_p_c Col_q_p_d neq_q_p) as Col_p_c_d.
		pose proof (by_prop_Col_order _ _ _ Col_p_c_d) as (_ & Col_c_d_p & _ & _ & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_c_d Col_A_B_p Col_c_d_p) as Meet_A_B_c_d.

		contradict Meet_A_B_c_d.
		exact n_Meet_A_B_c_d.
	}
	assert (neq_p_r := n_eq_p_r).
	pose proof (by_prop_neq_symmetric _ _ neq_p_r) as neq_r_p.


	assert (~ Col q d C) as n_Col_q_d_C.
	{
		intro Col_q_d_C.
		pose proof (by_prop_Col_order _ _ _ Col_q_d_C) as (_ & _ & _ & _ & Col_C_d_q).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_d_c Col_C_d_q neq_C_d) as Col_d_c_q.
		pose proof (by_prop_Col_order _ _ _ Col_d_c_q) as (_ & Col_c_q_d & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_c_q_d Col_c_q_p neq_c_q) as Col_q_d_p.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_q_d_p Col_q_d_r neq_q_d) as Col_d_p_r.

		pose proof (by_prop_Col_order _ _ _ Col_d_p_r) as (_ & Col_p_r_d & _ & _ & _).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_p_r_A Col_p_r_d neq_p_r) as Col_r_A_d.
		pose proof (by_prop_Col_order _ _ _ Col_r_A_d) as (Col_A_r_d & Col_A_d_r & Col_d_r_A & Col_r_d_A & Col_d_A_r).

		assert (~ neq B p) as n_neq_B_p.
		{
			intro neq_B_p.


			pose proof (lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB _ _ _ _ Col_A_r_d Col_A_r_B nCol_A_d_B) as eq_A_r.
			pose proof (by_prop_eq_symmetric _ _ eq_A_r) as eq_r_A.

			assert (Col p A d) as Col_p_A_d by (rewrite <- eq_r_A; exact Col_p_r_d).
			pose proof (by_prop_Col_order _ _ _ Col_p_A_d) as (Col_A_p_d & Col_A_d_p & Col_d_p_A & Col_p_d_A & Col_d_A_p).

			pose proof (lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB _ _ _ _ Col_A_p_d Col_A_p_B nCol_A_d_B) as eq_A_p.
			pose proof (by_prop_eq_symmetric _ _ eq_A_p) as eq_p_A.

			assert (eq r p) as eq_r_p by (rewrite eq_p_A; exact eq_r_A).
			assert (Col q p d) as Col_q_p_d by (rewrite <- eq_r_p; exact Col_q_r_d).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_q_p_c Col_q_p_d neq_q_p) as Col_p_c_d.
			pose proof (by_prop_Col_order _ _ _ Col_p_c_d) as (_ & Col_c_d_p & _ & _ & _).
			pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_c_d Col_A_B_p Col_c_d_p) as Meet_A_B_c_d.

			contradict Meet_A_B_c_d.
			exact n_Meet_A_B_c_d.
		}
		assert (eq_B_p := n_neq_B_p).
		apply Classical_Prop.NNPP in eq_B_p.

		assert (neq A p) as neq_A_p by (rewrite <- eq_B_p; exact neq_A_B).

		assert (~ eq r A) as n_eq_r_A.
		{
			intro eq_r_A.

			assert (Col d p A) as Col_d_p_A by (rewrite <- eq_r_A; exact Col_d_p_r).
			assert (Col d B A) as Col_d_B_A by (rewrite eq_B_p; exact Col_d_p_A).
			pose proof (by_prop_Col_order _ _ _ Col_d_B_A) as (_ & _ & _ & _ & Col_A_B_d).

			contradict Col_A_B_d.
			exact n_Col_A_B_d.
		}
		assert (neq_r_A := n_eq_r_A).

		assert (Col d B r) as Col_d_B_r by (rewrite eq_B_p; exact Col_d_p_r).
		pose proof (by_prop_Col_order _ _ _ Col_d_B_r) as (Col_B_d_r & Col_B_r_d & Col_r_d_B & Col_d_r_B & Col_r_B_d).

		pose proof (lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB _ _ _ _ Col_B_r_d Col_B_r_A nCol_B_d_A) as eq_B_r.

		pose proof (by_prop_eq_symmetric _ _ eq_B_r) as eq_r_B.
		pose proof (by_prop_eq_symmetric _ _ eq_B_p) as eq_p_B.
		assert (eq p r) as eq_p_r by (rewrite eq_r_B; exact eq_p_B).
		contradict eq_p_r.
		exact n_eq_p_r.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_q_d_C) as nCol_q_d_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_q_d_C) as (nCol_d_q_C & _ & _ & _ & _).

	pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_q_r_d BetS_C_c_d nCol_q_d_C) as (E & BetS_q_E_c & BetS_C_E_r).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_q_E_c) as Col_q_E_c.
	pose proof (by_prop_Col_order _ _ _ Col_q_E_c) as (_ & _ & _ & Col_q_c_E & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_E_r) as BetS_r_E_C.

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_q_c_p Col_q_c_E neq_q_c) as Col_c_p_E.
	pose proof (by_prop_Col_order _ _ _ Col_c_p_E) as (_ & _ & _ & Col_c_E_p & _).

	pose proof (lemma_extension _ _ _ _ neq_r_p neq_r_p) as (J & BetS_r_p_J & Cong_pJ_rp).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_r_p_J) as BetS_J_p_r.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_r_p_J) as (_ & _ & neq_r_J).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_r_p_J) as (neq_p_J & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_J_p_r) as (_ & _ & neq_J_r).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_J_p_r) as (_ & neq_J_p & _).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_r_p_J) as Col_r_p_J.
	pose proof (by_prop_Col_order _ _ _ Col_r_p_J) as (Col_p_r_J & Col_p_J_r & Col_J_r_p & Col_r_J_p & Col_J_p_r).


	assert (~ Meet C d J r) as n_Meet_C_d_J_r.
	{
		intro Meet_C_d_J_r.

		destruct Meet_C_d_J_r as (K & _ & _ & Col_C_d_K & Col_J_r_K).

		pose proof (by_prop_Col_order _ _ _ Col_C_d_K) as (Col_d_C_K & Col_d_K_C & Col_K_C_d & Col_C_K_d & Col_K_d_C).
		pose proof (by_prop_Col_order _ _ _ Col_J_r_K) as (Col_r_J_K & _ & _ & _ & _).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_d_c Col_C_d_K neq_C_d) as Col_d_c_K.
		pose proof (by_prop_Col_order _ _ _ Col_d_c_K) as (Col_c_d_K & Col_c_K_d & Col_K_d_c & Col_d_K_c & Col_K_c_d).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_r_J_p Col_r_J_K neq_r_J) as Col_J_p_K.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_J_p_K Col_J_p_r neq_J_p) as Col_p_K_r.
		pose proof (by_prop_Col_order _ _ _ Col_p_K_r) as (_ & _ & _ & Col_p_r_K & _).
		pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_p_r Col_p_r_A Col_p_r_B Col_p_r_K) as Col_A_B_K.

		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_c_d Col_A_B_K Col_c_d_K) as Meet_A_B_c_d.

		contradict Meet_A_B_c_d.
		exact n_Meet_A_B_c_d.
	}

	assert (eq c c) as eq_c_c by (reflexivity).
	assert (eq q q) as eq_q_q by (reflexivity).
	assert (eq d d) as eq_d_d by (reflexivity).
	assert (eq r r) as eq_r_r by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).

	pose proof (by_def_Col_from_eq_B_C q C C eq_C_C) as Col_q_C_C.
	pose proof (by_def_Col_from_eq_B_C d q q eq_q_q) as Col_d_q_q.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_d_q_C Col_d_q_r Col_d_q_q neq_r_q) as nCol_r_q_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_r_q_C) as (_ & _ & _ & nCol_r_C_q & _).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_d_q_C Col_d_q_q Col_d_q_r neq_q_r) as nCol_q_r_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_r_q_C) as (_ & nCol_q_C_r & _ & _ & _).


	pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_C_c_d Col_J_p_r neq_C_d neq_J_r neq_C_c neq_p_r n_Meet_C_d_J_r BetS_C_E_r Col_c_p_E) as BetS_c_E_p.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_E_p) as BetS_p_E_c.
	pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_q_p_c BetS_p_E_c) as BetS_q_p_E.

	pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_q_p_E BetS_r_E_C nCol_r_C_q) as (F & BetS_q_F_C & BetS_r_p_F).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_q_F_C) as BetS_C_F_q.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_q_F_C) as (neq_F_C & _ & _).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_q_F_C) as Col_q_F_C.
	pose proof (by_prop_Col_order _ _ _ Col_q_F_C) as (_ & _ & _ & Col_q_C_F & _).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_r_p_F) as Col_r_p_F.
	pose proof (by_prop_Col_order _ _ _ Col_r_p_F) as (Col_p_r_F & _ & _ & _ & _).

	pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_r_p Col_r_p_A Col_r_p_B Col_r_p_F) as Col_A_B_F.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_q_C_r Col_q_C_F Col_q_C_C neq_F_C) as nCol_F_C_r.
	pose proof (by_prop_nCol_order _ _ _ nCol_F_C_r) as (_ & _ & _ & nCol_F_r_C & _).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_p_r_A Col_p_r_F neq_p_r) as Col_r_A_F.
	pose proof (by_prop_Col_order _ _ _ Col_r_A_F) as (_ & _ & Col_F_r_A & _ & _).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_p_r_B Col_p_r_F neq_p_r) as Col_r_B_F.
	pose proof (by_prop_Col_order _ _ _ Col_r_B_F) as (_ & _ & Col_F_r_B & _ & _).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_F_r_C Col_F_r_A Col_F_r_B neq_A_B) as nCol_A_B_C.

	pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_A_B_F Col_A_B_r BetS_C_F_q BetS_d_r_q nCol_A_B_C nCol_A_B_d) as SameSide_C_d_AB.

	assert (~ Meet A B C d) as n_Meet_A_B_C_d.
	{
		intro Meet_A_B_C_d.

		destruct Meet_A_B_C_d as (K & _ & _ & Col_A_B_K & Col_C_d_K).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_d_c Col_C_d_K neq_C_d) as Col_d_c_K.
		pose proof (by_prop_Col_order _ _ _ Col_d_c_K) as (Col_c_d_K & _ & _ & _ & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_c_d Col_A_B_K Col_c_d_K) as Meet_A_B_c_d.

		contradict Meet_A_B_c_d.
		exact n_Meet_A_B_c_d.
	}

	pose proof (by_def_TarskiPar _ _ _ _ neq_A_B neq_C_d n_Meet_A_B_C_d SameSide_C_d_AB) as TarskiPar_AB_Cd.

	exact TarskiPar_AB_Cd.
Qed.

End Euclid.
