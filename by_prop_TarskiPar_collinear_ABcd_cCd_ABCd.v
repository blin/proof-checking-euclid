Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
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
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_TarskiPar_collinear_ABcd_cCd_ABCd :
	forall A B C c d,
	TarskiPar A B c d ->
	BetS c C d ->
	TarskiPar A B C d.
Proof.
	intros A B C c d.
	intros TarskiPar_AB_cd.
	intros BetS_c_C_d.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_C_d) as BetS_d_C_c.

	destruct TarskiPar_AB_cd as (neq_A_B & neq_c_d & n_Meet_A_B_c_d & SameSide_c_d_AB).

	destruct SameSide_c_d_AB as (q & p & r & Col_A_B_p & Col_A_B_r & BetS_c_p_q & BetS_d_r_q & nCol_A_B_c & nCol_A_B_d).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_c_C_d) as (neq_C_d & _ & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_p_q) as BetS_q_p_c.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_d_r_q) as BetS_q_r_d.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_q_p_c) as Col_q_p_c.

	assert (~ eq p r) as n_eq_p_r.
	{
		intro eq_p_r.
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_q_r_d) as Col_q_r_d.
		assert (Col q p d) as Col_q_p_d by (rewrite eq_p_r; exact Col_q_r_d).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_q_p_c) as (_ & neq_q_p & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_q_p_c Col_q_p_d neq_q_p) as Col_p_c_d.
		pose proof (by_prop_Col_order _ _ _ Col_p_c_d) as (_ & Col_c_d_p & _ & _ & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_c_d Col_A_B_p Col_c_d_p) as Meet_A_B_c_d.
		contradict Meet_A_B_c_d.
		exact n_Meet_A_B_c_d.
	}
	assert (neq_p_r := n_eq_p_r).


	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_B_c Col_A_B_p Col_A_B_r neq_p_r) as nCol_p_r_c.
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_B_d Col_A_B_p Col_A_B_r neq_p_r) as nCol_p_r_d.
	pose proof (by_prop_nCol_order _ _ _ nCol_p_r_d) as (_ & nCol_r_d_p & _ & _ & _).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_q_r_d) as Col_q_r_d.
	pose proof (by_prop_Col_order _ _ _ Col_q_r_d) as (_ & Col_r_d_q & _ & _ & _).
	assert (eq d d) as eq_d_d by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C r d d eq_d_d) as Col_r_d_d.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_q_r_d) as (_ & _ & neq_q_d).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_r_d_p Col_r_d_q Col_r_d_d neq_q_d) as nCol_q_d_p.
	pose proof (by_prop_nCol_order _ _ _ nCol_q_d_p) as (_ & _ & _ & nCol_q_p_d & _).
	assert (eq c c) as eq_c_c by (reflexivity).

	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_p_r_c) as n_Col_p_r_c.


	assert (~ eq c p) as n_eq_c_p.
	{
		intro eq_c_p.
		pose proof (by_prop_eq_symmetric _ _ eq_c_p) as eq_p_c.
		pose proof (by_def_Col_from_eq_A_C p r c eq_p_c) as Col_p_r_c.
		contradict Col_p_r_c.
		exact n_Col_p_r_c.
	}
	assert (neq_c_p := n_eq_c_p).


	assert (eq p p) as eq_p_p by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C q p p eq_p_p) as Col_q_p_p.
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_q_p_d Col_q_p_c Col_q_p_p neq_c_p) as nCol_c_p_d.
	pose proof (by_prop_Col_order _ _ _ Col_q_p_c) as (_ & _ & _ & _ & Col_c_p_q).
	pose proof (by_def_Col_from_eq_A_C c p c eq_c_c) as Col_c_p_c.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_q_p_c) as (_ & _ & neq_q_c).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_c_p_d Col_c_p_q Col_c_p_c neq_q_c) as nCol_q_c_d.
	pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_q_p_c BetS_d_C_c nCol_q_c_d) as (E & BetS_q_E_C & BetS_d_E_p).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_d_E_p) as BetS_p_E_d.
	pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_q_r_d BetS_p_E_d nCol_q_d_p) as (F & BetS_q_F_E & BetS_p_F_r).
	pose proof (by_def_Col_from_BetS_A_C_B _ _ _ BetS_p_F_r) as Col_p_r_F.
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_B_r Col_A_B_p neq_A_B) as Col_B_r_p.
	pose proof (by_prop_Col_order _ _ _ Col_A_B_p) as (Col_B_A_p & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_A_B_r) as (Col_B_A_r & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_Col_order _ _ _ Col_B_r_p) as (_ & _ & _ & Col_B_p_r & _).
	pose proof (by_prop_Col_order _ _ _ Col_A_B_p) as (_ & Col_B_p_A & _ & _ & _).

	assert (~ Col A B C) as n_Col_A_B_C.
	{
		intro Col_A_B_C.
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_c_C_d) as Col_c_C_d.
		pose proof (by_prop_Col_order _ _ _ Col_c_C_d) as (_ & _ & _ & Col_c_d_C & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_c_d Col_A_B_C Col_c_d_C) as Meet_A_B_c_d.
		contradict Meet_A_B_c_d.
		exact n_Meet_A_B_c_d.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_A_B_C) as nCol_A_B_C.

	pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_q_F_E BetS_q_E_C) as BetS_q_F_C.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_q_F_C) as BetS_C_F_q.

	assert (~ ~ SameSide C d A B) as n_n_SameSide_C_d_AB.
	{
		intro n_SameSide_C_d_AB.

		assert (~ neq B p) as n_neq_B_p.
		{
			intro neq_B_p.
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_p_r Col_B_p_A neq_B_p) as Col_p_r_A.
			pose proof (by_prop_Col_order _ _ _ Col_p_r_A) as (_ & _ & Col_A_p_r & _ & _).
			pose proof (by_prop_Col_order _ _ _ Col_B_A_p) as (_ & Col_A_p_B & _ & _ & _).

			assert (~ neq A p) as n_neq_A_p.
			{
				intro neq_A_p.
				pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_p_r Col_A_p_B neq_A_p) as Col_p_r_B.
				pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_p_r Col_p_r_A Col_p_r_B Col_p_r_F) as Col_A_B_F.
				pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_A_B_F Col_A_B_r BetS_C_F_q BetS_d_r_q nCol_A_B_C nCol_A_B_d) as SameSide_C_d_AB.
				contradict SameSide_C_d_AB.
				exact n_SameSide_C_d_AB.
			}
			assert (eq_A_p := n_neq_A_p).
			apply Classical_Prop.NNPP in eq_A_p.


			assert (Col A r F) as Col_A_r_F by (rewrite eq_A_p; exact Col_p_r_F).
			pose proof (by_prop_Col_order _ _ _ Col_A_r_F) as (Col_r_A_F & _ & _ & _ & _).
			pose proof (by_prop_Col_order _ _ _ Col_A_B_r) as (_ & _ & Col_r_A_B & _ & _).

			assert (~ eq r A) as n_eq_r_A.
			{
				intro eq_r_A.
				assert (eq r p) as eq_r_p by (rewrite eq_r_A; exact eq_A_p).
				pose proof (by_prop_neq_symmetric _ _ neq_p_r) as neq_r_p.
				contradict eq_r_p.
				exact neq_r_p.
			}
			assert (neq_r_A := n_eq_r_A).


			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_r_A_F Col_r_A_B neq_r_A) as Col_A_F_B.
			pose proof (by_prop_Col_order _ _ _ Col_A_F_B) as (_ & _ & _ & Col_A_B_F & _).
			pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_A_B_F Col_A_B_r BetS_C_F_q BetS_d_r_q nCol_A_B_C nCol_A_B_d) as SameSide_C_d_AB.
			contradict SameSide_C_d_AB.
			exact n_SameSide_C_d_AB.
		}
		assert (eq_B_p := n_neq_B_p).
		apply Classical_Prop.NNPP in eq_B_p.


		assert (neq A p) as neq_A_p by (rewrite <- eq_B_p; exact neq_A_B).
		pose proof (by_prop_Col_order _ _ _ Col_B_A_p) as (_ & Col_A_p_B & _ & _ & _).
		assert (eq A A) as eq_A_A by (reflexivity).
		pose proof (by_def_Col_from_eq_B_C B A A eq_A_A) as Col_B_A_A.
		pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_B_A Col_B_A_A Col_B_A_p Col_B_A_r) as Col_A_p_r.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_p_B Col_A_p_r neq_A_p) as Col_p_B_r.
		pose proof (by_prop_Col_order _ _ _ Col_B_p_r) as (_ & Col_p_r_B & _ & _ & _).
		pose proof (by_prop_Col_order _ _ _ Col_A_p_r) as (_ & Col_p_r_A & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_p_r Col_p_r_A Col_p_r_B Col_p_r_F) as Col_A_B_F.
		pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_A_B_F Col_A_B_r BetS_C_F_q BetS_d_r_q nCol_A_B_C nCol_A_B_d) as SameSide_C_d_AB.
		contradict SameSide_C_d_AB.
		exact n_SameSide_C_d_AB.
	}
	assert (SameSide_C_d_AB := n_n_SameSide_C_d_AB).
	apply Classical_Prop.NNPP in SameSide_C_d_AB.


	assert (~ Meet A B C d) as n_Meet_A_B_C_d.
	{
		intro Meet_A_B_C_d.

		destruct Meet_A_B_C_d as (R & _ & _ & Col_A_B_R & Col_C_d_R).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_c_C_d) as Col_c_C_d.
		pose proof (by_prop_Col_order _ _ _ Col_c_C_d) as (_ & Col_C_d_c & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_d_c Col_C_d_R neq_C_d) as Col_d_c_R.
		pose proof (by_prop_Col_order _ _ _ Col_d_c_R) as (Col_c_d_R & _ & _ & _ & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_c_d Col_A_B_R Col_c_d_R) as Meet_A_B_c_d.
		contradict Meet_A_B_c_d.
		exact n_Meet_A_B_c_d.
	}

	pose proof (by_def_TarskiPar _ _ _ _ neq_A_B neq_C_d n_Meet_A_B_C_d SameSide_C_d_AB) as TarskiPar_AB_Cd.

	exact TarskiPar_AB_Cd.
Qed.

End Euclid.
