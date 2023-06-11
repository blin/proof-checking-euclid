Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_betweennesspreserved.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearright.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_extensionunique.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_pointreflectionisometry.
Require Import ProofCheckingEuclid.lemma_right_triangle_NC.
Require Import ProofCheckingEuclid.lemma_right_triangle_leg_change.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
Require Import ProofCheckingEuclid.lemma_rightreverse.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_midpoint.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.proposition_10.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_linereflectionisometry :
	forall A B C D E F,
	RightTriangle B A C ->
	RightTriangle A B D ->
	BetS C A E ->
	BetS D B F ->
	Cong A C A E ->
	Cong B D B F ->
	Cong C D E F.
Proof.
	intros A B C D E F.
	intros RightTriangle_B_A_C.
	intros RightTriangle_A_B_D.
	intros BetS_C_A_E.
	intros BetS_D_B_F.
	intros Cong_A_C_A_E.
	intros Cong_B_D_B_F.

	pose proof (cn_congruencereflexive A C) as Cong_A_C_A_C.
	pose proof (cn_congruencereverse B F) as Cong_B_F_F_B.

	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_B_A_C) as RightTriangle_C_A_B.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_A_B_D) as RightTriangle_D_B_A.

	assert (RightTriangle_A_B_D2 := RightTriangle_A_B_D).
	destruct RightTriangle_A_B_D2 as (G & BetS_A_B_G & _ & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_G) as BetS_G_B_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_G) as (neq_B_G & neq_A_B & neq_A_G).
	pose proof (lemma_betweennotequal _ _ _ BetS_G_B_A) as (neq_B_A & neq_G_B & neq_G_A).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_A_E) as BetS_E_A_C.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_B_F) as BetS_F_B_D.
	pose proof (lemma_betweennotequal _ _ _ BetS_D_B_F) as (neq_B_F & neq_D_B & neq_D_F).
	pose proof (lemma_betweennotequal _ _ _ BetS_F_B_D) as (neq_B_D & neq_F_B & neq_F_D).

	pose proof (lemma_s_col_BetS_A_B_C D B F BetS_D_B_F) as Col_D_B_F.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_A_C_A_E) as (_ & Cong_C_A_A_E & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_A_C_A_E) as Cong_A_E_A_C.
	pose proof (lemma_doublereverse _ _ _ _ Cong_C_A_A_E) as (Cong_E_A_A_C & _).

	pose proof (lemma_s_midpoint _ _ _ BetS_E_A_C Cong_E_A_A_C) as Midpoint_E_A_C.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_B_D_B_F) as (_ & Cong_D_B_B_F & _).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_B_D_B_F Cong_B_F_F_B) as Cong_B_D_F_B.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_D_B_B_F) as Cong_B_F_D_B.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_B_F_D_B) as (_ & Cong_F_B_D_B & _).

	pose proof (proposition_10 _ _ neq_A_B) as (M & BetS_A_M_B & Cong_M_A_M_B).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_M_B) as BetS_B_M_A.
	
	pose proof (lemma_s_onray_assert_bets_AEB B A M BetS_B_M_A neq_B_A) as OnRay_B_A_M.
	pose proof (lemma_s_onray_assert_bets_AEB A B M BetS_A_M_B neq_A_B) as OnRay_A_B_M.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_M_A_M_B) as Cong_M_B_M_A.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_M_B_M_A) as (_ & Cong_B_M_M_A & _).
	pose proof (lemma_s_midpoint _ _ _ BetS_B_M_A Cong_B_M_M_A) as Midpoint_B_M_A.

	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_D_B_A OnRay_B_A_M) as RightTriangle_D_B_M.
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_C_A_B OnRay_A_B_M) as RightTriangle_C_A_M.

	pose proof (lemma_collinearright _ _ _ _ RightTriangle_D_B_A Col_D_B_F neq_F_B) as RightTriangle_F_B_A.
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_F_B_A OnRay_B_A_M) as RightTriangle_F_B_M.

	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_D_B_M) as nCol_D_B_M.
	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_F_B_M) as nCol_F_B_M.
	pose proof (lemma_NCdistinct _ _ _ nCol_D_B_M) as (_ & _ & neq_D_M & _ & _ & neq_M_D).
	pose proof (lemma_NCdistinct _ _ _ nCol_F_B_M) as (_ & _ & neq_F_M & _ & _ & neq_M_F).

	pose proof (lemma_rightreverse _ _ _ _ RightTriangle_C_A_M BetS_C_A_E Cong_C_A_A_E) as Cong_C_M_E_M.
	pose proof (lemma_rightreverse _ _ _ _ RightTriangle_D_B_M BetS_D_B_F Cong_D_B_B_F) as Cong_D_M_F_M.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_D_M_F_M) as Cong_F_M_D_M.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_C_M_E_M) as Cong_E_M_C_M.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_F_M_D_M) as (Cong_M_F_M_D & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_E_M_C_M) as (Cong_M_E_M_C & _ & _).

	pose proof (lemma_extension D M M D neq_D_M neq_M_D) as (R & BetS_D_M_R & Cong_M_R_M_D).
	pose proof (lemma_extension F M M F neq_F_M neq_M_F) as (Q & BetS_F_M_Q & Cong_M_Q_M_F).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_M_Q) as BetS_Q_M_F.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_M_R) as BetS_R_M_D.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_M_R_M_D) as Cong_M_D_M_R.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_M_Q_M_F) as Cong_M_F_M_Q.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_M_Q_M_F) as (Cong_Q_M_F_M & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_M_D_M_R) as (_ & Cong_D_M_M_R & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_M_F_M_Q) as (_ & Cong_F_M_M_Q & _).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_F_M_D_M Cong_D_M_M_R) as Cong_F_M_M_R.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_Q_M_F_M Cong_F_M_D_M) as Cong_Q_M_D_M.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_Q_M_D_M Cong_D_M_M_R) as Cong_Q_M_M_R.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_Q_M_M_R) as (_ & _ & Cong_Q_M_R_M).

	pose proof (lemma_s_midpoint _ _ _ BetS_D_M_R Cong_D_M_M_R) as Midpoint_D_M_R.
	pose proof (lemma_s_midpoint _ _ _ BetS_F_M_Q Cong_F_M_M_Q) as Midpoint_F_M_Q.

	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_D_M_R Midpoint_B_M_A neq_D_B) as Cong_D_B_R_A.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_D_M_R Midpoint_F_M_Q neq_D_F) as Cong_D_F_R_Q.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_F_M_Q Midpoint_B_M_A neq_F_B) as Cong_F_B_Q_A.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_F_B_Q_A) as Cong_Q_A_F_B.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_Q_A_F_B Cong_F_B_D_B) as Cong_Q_A_D_B.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_Q_A_D_B Cong_D_B_R_A) as Cong_Q_A_R_A.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_Q_A_R_A) as (_ & _ & Cong_Q_A_A_R).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_D_F_R_Q) as (Cong_F_D_Q_R & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_D_B_R_A) as (Cong_B_D_A_R & _ & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_B_D_A_R) as Cong_A_R_B_D.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_A_R_B_D Cong_B_D_B_F) as Cong_A_R_B_F.

	pose proof (lemma_betweennesspreserved _ _ _ _ _ _ Cong_F_B_Q_A Cong_F_D_Q_R Cong_B_D_A_R BetS_F_B_D) as BetS_Q_A_R.

	pose proof (lemma_s_midpoint _ _ _ BetS_Q_A_R Cong_Q_A_A_R) as Midpoint_Q_A_R.

	(* assert by cases *)
	assert (eq E Q \/ neq E Q) as [eq_E_Q|neq_E_Q] by (apply Classical_Prop.classic).
	{
		(* case eq_E_Q *)
		assert (Midpoint F M E) as Midpoint_F_M_E by (rewrite eq_E_Q; exact Midpoint_F_M_Q).
		assert (Cong F M M E) as Cong_F_M_M_E by (rewrite eq_E_Q; exact Cong_F_M_M_Q).
		assert (BetS F M E) as BetS_F_M_E by (rewrite eq_E_Q; exact BetS_F_M_Q).

		pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_F_M_E Midpoint_B_M_A neq_F_B) as Cong_F_B_E_A.
		pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_F_M_E Midpoint_D_M_R neq_F_D) as Cong_F_D_E_R.

		pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_D_M_F_M Cong_F_M_M_E) as Cong_D_M_M_E.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_D_M_M_E) as (_ & Cong_M_D_M_E & _).

		pose proof (lemma_congruenceflip _ _ _ _ Cong_F_B_E_A) as (Cong_B_F_A_E & _ & _).
		pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_A_R_B_F Cong_B_F_A_E) as Cong_A_R_A_E.
		pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_A_R_A_E Cong_A_E_A_C) as Cong_A_R_A_C.

		pose proof (lemma_betweennesspreserved _ _ _ _ _ _ Cong_F_B_E_A Cong_F_D_E_R Cong_B_D_A_R BetS_F_B_D) as BetS_E_A_R.

		pose proof (lemma_extensionunique _ _ _ _ BetS_E_A_R BetS_E_A_C Cong_A_R_A_C) as eq_R_C.
		assert (Cong F M M C) as Cong_F_M_M_C by (rewrite <- eq_R_C; exact Cong_F_M_M_R).
		assert (BetS C M D) as BetS_C_M_D by (rewrite <- eq_R_C; exact BetS_R_M_D).

		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_F_M_M_C) as Cong_M_C_F_M.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_M_C_F_M) as (_ & Cong_C_M_F_M & _).

		pose proof (cn_sumofparts _ _ _ _ _ _ Cong_C_M_F_M Cong_M_D_M_E BetS_C_M_D BetS_F_M_E) as Cong_C_D_F_E.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_C_D_F_E) as (_ & _ & Cong_C_D_E_F).

		exact Cong_C_D_E_F.
	}
	{
		(* case neq_E_Q *)
		pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_E_A_C Midpoint_Q_A_R neq_E_Q) as Cong_E_Q_C_R.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_E_Q_C_R) as (Cong_Q_E_R_C & _ & _).

		(* TODO: write out axiom_5_line *)
		pose proof (axiom_5_line _ _ _ _ _ _ _ _ Cong_M_F_M_D Cong_Q_E_R_C Cong_M_E_M_C BetS_Q_M_F BetS_R_M_D Cong_Q_M_R_M) as Cong_E_F_C_D.
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_E_F_C_D) as Cong_C_D_E_F.

		exact Cong_C_D_E_F.
	}
Qed.

End Euclid.
