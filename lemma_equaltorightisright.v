Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_right_triangle_leg_change.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
Require Import ProofCheckingEuclid.lemma_s_right_triangle.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_equaltorightisright :
	forall A B C a b c,
	RightTriangle A B C ->
	CongA a b c A B C ->
	RightTriangle a b c.
Proof.
	intros A B C a b c.
	intros RightTriangle_A_B_C.
	intros CongA_a_b_c_A_B_C.

	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_a_b_c_A_B_C) as CongA_A_B_C_a_b_c.

	destruct CongA_A_B_C_a_b_c as (E & F & e & f & OnRay_B_A_E & OnRay_B_C_F & OnRay_b_a_e & OnRay_b_c_f & Cong_B_E_b_e & Cong_B_F_b_f & Cong_E_F_e_f & nCol_A_B_C).
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_A_B_C OnRay_B_C_F) as RightTriangle_A_B_F.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_A_B_F) as RightTriangle_F_B_A.
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_F_B_A OnRay_B_A_E) as RightTriangle_F_B_E.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_F_B_E) as RightTriangle_E_B_F.
	pose proof (lemma_onray_strict _ _ _ OnRay_B_A_E) as neq_B_E.
	pose proof (lemma_inequalitysymmetric _ _ neq_B_E) as neq_E_B.

	destruct RightTriangle_E_B_F as (W & BetS_E_B_W & Cong_E_B_W_B & Cong_E_F_W_F & neq_B_F).
	pose proof (axiom_nocollapse _ _ _ _ neq_B_E Cong_B_E_b_e) as neq_b_e.
	pose proof (lemma_inequalitysymmetric _ _ neq_b_e) as neq_e_b.
	pose proof (lemma_extension e b e b neq_e_b neq_e_b) as (w & BetS_e_b_w & Cong_b_w_e_b).
	pose proof (lemma_doublereverse _ _ _ _ Cong_B_E_b_e) as (Cong_e_b_E_B & _).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_b_w_e_b Cong_e_b_E_B) as Cong_b_w_E_B.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_E_B_W_B) as (_ & _ & Cong_E_B_B_W).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_b_w_E_B Cong_E_B_B_W) as Cong_b_w_B_W.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_B_F_b_f) as Cong_b_f_B_F.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_E_F_e_f) as Cong_e_f_E_F.
	pose proof (cn_sumofparts _ _ _ _ _ _ Cong_e_b_E_B Cong_b_w_B_W BetS_e_b_w BetS_E_B_W) as Cong_e_w_E_W.
	pose proof (axiom_5_line _ _ _ _ _ _ _ _ Cong_b_w_B_W Cong_e_f_E_F Cong_b_f_B_F BetS_e_b_w BetS_E_B_W Cong_e_b_E_B) as Cong_f_w_F_W.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_e_b_E_B Cong_E_B_B_W) as Cong_e_b_B_W.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_b_w_B_W) as Cong_B_W_b_w.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_e_b_B_W Cong_B_W_b_w) as Cong_e_b_b_w.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_e_b_b_w) as (_ & _ & Cong_e_b_w_b).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_e_f_E_F Cong_E_F_W_F) as Cong_e_f_W_F.
	pose proof (lemma_doublereverse _ _ _ _ Cong_f_w_F_W) as (Cong_W_F_w_f & _).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_e_f_W_F Cong_W_F_w_f) as Cong_e_f_w_f.
	pose proof (lemma_onray_strict _ _ _ OnRay_b_c_f) as neq_b_f.
	pose proof (lemma_s_right_triangle _ _ _ _ BetS_e_b_w Cong_e_b_w_b Cong_e_f_w_f neq_b_f) as RightTriangle_e_b_f.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_b_c_f) as OnRay_b_f_c.
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_e_b_f OnRay_b_f_c) as RightTriangle_e_b_c.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_e_b_c) as RightTriangle_c_b_e.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_b_a_e) as OnRay_b_e_a.
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_c_b_e OnRay_b_e_a) as RightTriangle_c_b_a.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_c_b_a) as RightTriangle_a_b_c.

	exact RightTriangle_a_b_c.
Qed.

End Euclid.
