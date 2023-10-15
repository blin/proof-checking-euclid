Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col .
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol .
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongTriangles_reflexive.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:area}.

Lemma by_prop_EqAreaQuad_reflexive :
	forall a b c d p,
	BetS a p c ->
	BetS b p d ->
	nCol a b c ->
	EqAreaQuad a b c d a b c d.
Proof.
	intros a b c d p.
	intros BetS_a_p_c.
	intros BetS_b_p_d.
	intros nCol_a_b_c.

	pose proof (by_prop_nCol_order _ _ _ nCol_a_b_c) as (_ & _ & _ & nCol_a_c_b & _).
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_a_b_c) as n_Col_a_b_c.

	assert (~ Col a c d) as n_Col_a_c_d.
	{
		intro Col_a_c_d.
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_b_p_d) as Col_b_p_d.
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_a_p_c) as Col_a_p_c.
		pose proof (by_prop_Col_order _ _ _ Col_a_p_c) as (_ & _ & _ & Col_a_c_p & _).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_a_p_c) as (_ & _ & neq_a_c).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_a_c_d Col_a_c_p neq_a_c) as Col_c_d_p.
		pose proof (by_prop_Col_order _ _ _ Col_c_d_p) as (_ & Col_d_p_c & _ & _ & _).
		pose proof (by_prop_Col_order _ _ _ Col_b_p_d) as (_ & _ & _ & _ & Col_d_p_b).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_b_p_d) as (neq_p_d & _ & _).
		pose proof (by_prop_neq_symmetric _ _ neq_p_d) as neq_d_p.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_d_p_c Col_d_p_b neq_d_p) as Col_p_c_b.
		pose proof (by_prop_Col_order _ _ _ Col_a_p_c) as (_ & Col_p_c_a & _ & _ & _).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_a_p_c) as (neq_p_c & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_p_c_b Col_p_c_a neq_p_c) as Col_c_b_a.
		pose proof (by_prop_Col_order _ _ _ Col_c_b_a) as (_ & _ & _ & _ & Col_a_b_c).
		contradict Col_a_b_c.
		exact n_Col_a_b_c.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_a_c_d) as nCol_a_c_d.

	pose proof (by_def_Triangle _ _ _ nCol_a_c_d) as Triangle_acd.
	pose proof (by_def_Triangle _ _ _ nCol_a_c_b) as Triangle_acb.
	pose proof (by_prop_CongTriangles_reflexive _ _ _ Triangle_acd) as CongTriangles_acd_acd.
	pose proof (by_prop_CongTriangles_reflexive _ _ _ Triangle_acb) as CongTriangles_acb_acb.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_acd_acd) as EqAreaTri_a_c_d_a_c_d.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_acb_acb) as EqAreaTri_a_c_b_a_c_b.
	pose proof (by_def_Col_from_BetS_A_C_B _ _ _ BetS_a_p_c) as Col_a_c_p.
	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_b_p_d Col_a_c_p nCol_a_c_b) as OppositeSide_b_ac_d.

	assert (OppositeSide_b_ac_d_2 := OppositeSide_b_ac_d).
	destruct OppositeSide_b_ac_d_2 as (M & BetS_b_M_d & Col_a_c_M & _).

	assert (BetS a p c \/ eq a p \/ eq p c) as BetS_a_p_c_or_eq_a_p_or_eq_p_c by (left; exact BetS_a_p_c).

	pose proof (
		axiom_paste3
		a c b d p a c b d p
		EqAreaTri_a_c_b_a_c_b
		EqAreaTri_a_c_d_a_c_d
		BetS_b_p_d BetS_a_p_c_or_eq_a_p_or_eq_p_c
		BetS_b_p_d BetS_a_p_c_or_eq_a_p_or_eq_p_c
	) as EqAreaQuad_a_b_c_d_a_b_c_d.

	exact EqAreaQuad_a_b_c_d_a_b_c_d.
Qed.

End Euclid.
