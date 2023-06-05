Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_droppedperpendicularunique.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_extensionunique.
Require Import ProofCheckingEuclid.lemma_right_triangle_NC.
Require Import ProofCheckingEuclid.lemma_right_triangle_leg_change.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_right_triangle.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_right_triangle_CBA_n_ACB :
	forall A B C,
	RightTriangle C B A ->
	~ RightTriangle A C B.
Proof.
	intros A B C.
	intros RightTriangle_C_B_A.

	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_C_B_A) as nCol_C_B_A.
	pose proof (lemma_NCdistinct _ _ _ nCol_C_B_A) as (neq_C_B & neq_B_A & neq_C_A & neq_B_C & neq_A_B & neq_A_C).
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_C_B_A) as RightTriangle_A_B_C.
	pose proof (lemma_extension B C C B neq_B_C neq_C_B) as (E & BetS_B_C_E & Cong_C_E_C_B).
	pose proof (lemma_s_col_BetS_A_B_C B C E BetS_B_C_E) as Col_B_C_E.
	pose proof (lemma_collinearorder _ _ _ Col_B_C_E) as (_ & _ & _ & _ & Col_E_C_B).
	pose proof (lemma_s_onray_assert_bets_ABE B C E BetS_B_C_E neq_B_C) as OnRay_B_C_E.
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_A_B_C OnRay_B_C_E) as RightTriangle_A_B_E.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_A_B_E) as RightTriangle_E_B_A.

	assert (~ RightTriangle A C B) as n_RightTriangle_A_C_B.
	{
		intro RightTriangle_A_C_B.
		pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_A_C_B) as RightTriangle_B_C_A.
		
		destruct RightTriangle_B_C_A as (F & BetS_B_C_F & Cong_B_C_F_C & Cong_B_A_F_A & _).
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_B_C_F_C) as Cong_F_C_B_C.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_F_C_B_C) as (_ & Cong_C_F_B_C & _).
		pose proof (lemma_congruenceflip _ _ _ _ Cong_C_E_C_B) as (_ & _ & Cong_C_E_B_C).
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_C_E_B_C) as Cong_B_C_C_E.
		pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_C_F_B_C Cong_B_C_C_E) as Cong_C_F_C_E.
		pose proof (lemma_extensionunique _ _ _ _ BetS_B_C_F BetS_B_C_E Cong_C_F_C_E) as eq_F_E.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_C_E) as BetS_E_C_B.
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_B_A_F_A) as Cong_F_A_B_A.
		
		assert (Cong E A B A) as Cong_E_A_B_A by (rewrite <- eq_F_E; exact Cong_F_A_B_A).

		pose proof (lemma_congruenceflip _ _ _ _ Cong_C_E_C_B) as (Cong_E_C_B_C & _ & _).
		epose proof (lemma_s_right_triangle E C A B BetS_E_C_B Cong_E_C_B_C Cong_E_A_B_A neq_C_A) as RightTriangle_E_C_A.
		pose proof (lemma_droppedperpendicularunique _ _ _ _ RightTriangle_E_C_A RightTriangle_E_B_A Col_E_C_B) as eq_C_B.
		contradict eq_C_B.
		exact neq_C_B.
	}

	exact n_RightTriangle_A_C_B.
Qed.

End Euclid.
