Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_TogetherGreater_flip.
Require Import ProofCheckingEuclid.lemma_TogetherGreater_symmetric.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_right_triangle_NC.
Require Import ProofCheckingEuclid.lemma_right_triangle_leg_change.
Require Import ProofCheckingEuclid.lemma_right_triangle_same_base_cong_side_cong_hypotenuse.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
Require Import ProofCheckingEuclid.lemma_rightreverse.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_conga.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_right_triangle.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.proposition_20.
Require Import ProofCheckingEuclid.proposition_22.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_Euclid4 :
	forall A B C a b c,
	RightTriangle A B C ->
	RightTriangle a b c ->
	CongA A B C a b c.
Proof.
	intros A B C a b c.
	intros RightTriangle_A_B_C.
	intros RightTriangle_a_b_c.


	assert (RightTriangle_A_B_C2 := RightTriangle_A_B_C).
	destruct RightTriangle_A_B_C2 as (D & BetS_A_B_D & Cong_A_B_D_B & Cong_A_C_D_C & neq_B_C).
	assert (RightTriangle_a_b_c2 := RightTriangle_a_b_c).
	destruct RightTriangle_a_b_c2 as (d & BetS_a_b_d & Cong_a_b_d_b & Cong_a_c_d_c & neq_b_c).

	pose proof (lemma_betweennotequal _ _ _ BetS_a_b_d) as (_ & neq_a_b & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_a_b) as neq_b_a.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_D) as (_ & neq_A_B & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.
	pose proof (lemma_layoff _ _ _ _ neq_b_a neq_B_A) as (p & OnRay_b_a_p & Cong_b_p_B_A).
	pose proof (lemma_layoff _ _ _ _ neq_b_c neq_B_C) as (q & OnRay_b_c_q & Cong_b_q_B_C).
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_a_b_c OnRay_b_c_q) as RightTriangle_a_b_q.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_a_b_q) as RightTriangle_q_b_a.
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_q_b_a OnRay_b_a_p) as RightTriangle_q_b_p.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_q_b_p) as RightTriangle_p_b_q.

	assert (RightTriangle_p_b_q2 := RightTriangle_p_b_q).
	destruct RightTriangle_p_b_q2 as (r & BetS_p_b_r & Cong_p_b_r_b & Cong_p_q_r_q & neq_b_q).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_p_q_r_q) as (Cong_q_p_q_r & _ & _).
	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_p_b_q) as nCol_p_b_q.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_p_b_q) as n_Col_p_b_q.

	assert (~ Col b q p) as n_Col_b_q_p.
	{
		intro Col_b_q_p.
		pose proof (lemma_collinearorder _ _ _ Col_b_q_p) as (_ & _ & Col_p_b_q & _ & _).
		contradict Col_p_b_q.
		exact n_Col_p_b_q.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_b_q_p) as nCol_b_q_p.


	assert (~ Col q p b) as n_Col_q_p_b.
	{
		intro Col_q_p_b.
		pose proof (lemma_collinearorder _ _ _ Col_q_p_b) as (_ & Col_p_b_q & _ & _ & _).
		contradict Col_p_b_q.
		exact n_Col_p_b_q.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_q_p_b) as nCol_q_p_b.

	pose proof (lemma_s_triangle _ _ _ nCol_p_b_q) as Triangle_p_b_q.
	pose proof (lemma_s_triangle _ _ _ nCol_b_q_p) as Triangle_b_q_p.
	pose proof (lemma_s_triangle _ _ _ nCol_q_p_b) as Triangle_q_p_b.
	pose proof (proposition_20 _ _ _ Triangle_p_b_q) as TogetherGreater_b_p_p_q_b_q.
	pose proof (proposition_20 _ _ _ Triangle_b_q_p) as TogetherGreater_q_b_b_p_q_p.
	pose proof (proposition_20 _ _ _ Triangle_q_p_b) as TogetherGreater_p_q_q_b_p_b.
	pose proof (lemma_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_q_b_b_p_q_p) as (TogetherGreater_b_q_b_p_q_p & _).
	pose proof (lemma_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_b_q_b_p_q_p) as (_ & TogetherGreater_b_q_b_p_p_q).
	pose proof (lemma_TogetherGreater_symmetric _ _ _ _ _ _ TogetherGreater_p_q_q_b_p_b) as TogetherGreater_q_b_p_q_p_b.
	pose proof (lemma_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_q_b_p_q_p_b) as (TogetherGreater_b_q_p_q_p_b & _).
	pose proof (lemma_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_b_q_p_q_p_b) as (_ & TogetherGreater_b_q_p_q_b_p).
	pose proof (lemma_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_b_p_p_q_b_q) as (_ & TogetherGreater_b_p_p_q_q_b).
	pose proof (proposition_22 _ _ _ _ _ _ _ _ TogetherGreater_b_q_b_p_p_q TogetherGreater_b_q_p_q_b_p TogetherGreater_b_p_p_q_b_q neq_B_A) as (E & F & Cong_B_E_b_p & Cong_B_F_b_q & Cong_E_F_p_q & OnRay_B_A_E & Triangle_B_E_F).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_D) as BetS_D_B_A.
	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB B A neq_B_A) as OnRay_B_A_A.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_B_E_b_p Cong_b_p_B_A) as Cong_B_E_B_A.
	pose proof (lemma_layoffunique _ _ _ _ OnRay_B_A_E OnRay_B_A_A Cong_B_E_B_A) as eq_E_A.
	assert (Cong B A b p) as Cong_B_A_b_p by (rewrite <- eq_E_A; exact Cong_B_E_b_p).
	assert (Cong A F p q) as Cong_A_F_p_q by (rewrite <- eq_E_A; exact Cong_E_F_p_q).

	assert (~ eq p b) as n_eq_p_b.
	{
		intro eq_p_b.
		pose proof (lemma_s_col_eq_A_B p b q eq_p_b) as Col_p_b_q.
		contradict Col_p_b_q.
		exact n_Col_p_b_q.
	}
	assert (neq_p_b := n_eq_p_b).


	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_p_b_r_b) as Cong_r_b_p_b.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_r_b_p_b) as (_ & Cong_b_r_p_b & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_B_E_b_p) as Cong_b_p_B_E.
	pose proof (lemma_inequalitysymmetric _ _ neq_p_b) as neq_b_p.
	pose proof (cn_congruencereverse B A) as Cong_B_A_A_B.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_b_r_p_b) as Cong_p_b_b_r.
	pose proof (lemma_doublereverse _ _ _ _ Cong_B_A_b_p) as (Cong_p_b_A_B & _).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_b_r_p_b Cong_p_b_A_B) as Cong_b_r_A_B.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_A_B_D_B) as (_ & _ & Cong_A_B_B_D).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_b_r_A_B Cong_A_B_B_D) as Cong_b_r_B_D.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_B_F_b_q) as Cong_b_q_B_F.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_A_F_p_q) as Cong_p_q_A_F.
	pose proof (axiom_5_line _ _ _ _ _ _ _ _ Cong_b_r_B_D Cong_p_q_A_F Cong_b_q_B_F BetS_p_b_r BetS_A_B_D Cong_p_b_A_B) as Cong_q_r_F_D.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_A_F_p_q Cong_p_q_r_q) as Cong_A_F_r_q.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_A_F_r_q) as (_ & _ & Cong_A_F_q_r).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_A_F_q_r Cong_q_r_F_D) as Cong_A_F_F_D.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_A_F_F_D) as (_ & _ & Cong_A_F_D_F).
	pose proof (cn_congruencereverse q b) as Cong_q_b_b_q.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_q_b_b_q Cong_b_q_B_F) as Cong_q_b_B_F.
	pose proof (axiom_nocollapse _ _ _ _ neq_b_q Cong_b_q_B_F) as neq_B_F.
	pose proof (lemma_s_right_triangle _ _ _ _ BetS_A_B_D Cong_A_B_D_B Cong_A_F_D_F neq_B_F) as RightTriangle_A_B_F.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_b_q_B_C) as Cong_B_C_b_q.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_B_C_b_q Cong_b_q_B_F) as Cong_B_C_B_F.
	pose proof (lemma_right_triangle_same_base_cong_side_cong_hypotenuse _ _ _ _ RightTriangle_A_B_C RightTriangle_A_B_F Cong_B_C_B_F) as Cong_A_C_A_F.
	assert (eq F F) as eq_F_F by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB B F neq_B_F) as OnRay_B_F_F.
	pose proof (lemma_s_onray_assert_ABB B C neq_B_C) as OnRay_B_C_C.
	pose proof (cn_congruencereflexive B A) as Cong_B_A_B_A.
	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_A_B_C) as nCol_A_B_C.
	pose proof (lemma_s_conga _ _ _ _ _ _ _ _ _ _ OnRay_B_A_A OnRay_B_C_C OnRay_B_A_A OnRay_B_F_F Cong_B_A_B_A Cong_B_C_B_F Cong_A_C_A_F nCol_A_B_C) as CongA_A_B_C_A_B_F.
	pose proof (lemma_equalanglesreflexive _ _ _ nCol_A_B_C) as CongA_A_B_C_A_B_C.
	assert (eq p p) as eq_p_p by (reflexivity).
	assert (eq q q) as eq_q_q by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB b p neq_b_p) as OnRay_b_p_p.
	pose proof (lemma_s_onray_assert_ABB b q neq_b_q) as OnRay_b_q_q.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_B_A_b_p) as (_ & _ & Cong_B_A_p_b).
	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_A_B_F) as nCol_A_B_F.
	pose proof (lemma_s_conga _ _ _ _ _ _ _ _ _ _ OnRay_B_A_E OnRay_B_F_F OnRay_b_p_p OnRay_b_q_q Cong_B_E_b_p Cong_B_F_b_q Cong_E_F_p_q nCol_A_B_F) as CongA_A_B_F_p_b_q.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_B_C_A_B_F CongA_A_B_F_p_b_q) as CongA_A_B_C_p_b_q.
	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_a_b_c) as nCol_a_b_c.
	pose proof (cn_congruencereflexive b p) as Cong_b_p_b_p.
	pose proof (cn_congruencereflexive b q) as Cong_b_q_b_q.
	pose proof (cn_congruencereflexive p q) as Cong_p_q_p_q.
	pose proof (lemma_s_conga _ _ _ _ _ _ _ _ _ _ OnRay_b_a_p OnRay_b_c_q OnRay_b_p_p OnRay_b_q_q Cong_b_p_b_p Cong_b_q_b_q Cong_p_q_p_q nCol_a_b_c) as CongA_a_b_c_p_b_q.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_a_b_c_p_b_q) as CongA_p_b_q_a_b_c.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_B_C_p_b_q CongA_p_b_q_a_b_c) as CongA_A_B_C_a_b_c.

	exact CongA_A_B_C_a_b_c.
Qed.

End Euclid.

