Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_s_incirc_within_radius.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_perp_at.
Require Import ProofCheckingEuclid.lemma_s_right_triangle.
Require Import ProofCheckingEuclid.proposition_10.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_12 :
	forall A B C,
	nCol A B C ->
	exists X, Perp_at C X A B X.
Proof.
	intros A B C.
	intros nCol_A_B_C.

	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_B_C) as neq_C_B.

	pose proof (postulate_Euclid2 _ _ neq_C_B) as (E & BetS_C_B_E).
	pose proof (lemma_betweennotequal _ _ _ BetS_C_B_E) as (_ & _ & neq_C_E).
	pose proof (postulate_Euclid3 _ _ neq_C_E) as (K & CI_K_C_CE).

	pose proof (cn_congruencereflexive C E) as Cong_CE_CE.
	pose proof (cn_congruencereflexive C B) as Cong_CB_CB.
	pose proof (
		lemma_s_incirc_within_radius _ _ _ _ _ _ _ CI_K_C_CE BetS_C_B_E Cong_CE_CE Cong_CB_CB
	) as InCirc_B_K.

	pose proof (
		postulate_line_circle _ _ _ _ _ _ CI_K_C_CE InCirc_B_K neq_A_B
	) as (P & Q & Col_A_B_P & BetS_A_B_Q & OnCirc_P_K & OnCirc_Q_K & BetS_P_B_Q).


	pose proof (lemma_betweennotequal _ _ _ BetS_P_B_Q) as (neq_B_Q & _ & neq_P_Q).
	pose proof (proposition_10 _ _ neq_P_Q) as (M & BetS_P_M_Q & Cong_MP_MQ).

	assert (Col P M Q) as Col_P_M_Q by (unfold Col; one_of_disjunct BetS_P_M_Q).
	assert (Col P B Q) as Col_P_B_Q by (unfold Col; one_of_disjunct BetS_P_B_Q).
	pose proof (lemma_collinearorder _ _ _ Col_P_M_Q) as (_ & _ & _ & Col_P_Q_M & _).
	pose proof (lemma_collinearorder _ _ _ Col_P_B_Q) as (_ & _ & _ & Col_P_Q_B & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_P_Q_B Col_P_Q_M neq_P_Q) as Col_Q_B_M.
	assert (Col A B Q) as Col_A_B_Q by (unfold Col; one_of_disjunct BetS_A_B_Q).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_Q) as (_ & _ & _ & _ & Col_Q_B_A).
	pose proof (lemma_inequalitysymmetric _ _ neq_B_Q) as neq_Q_B.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_B_M Col_Q_B_A neq_Q_B) as Col_B_M_A.
	pose proof (lemma_collinearorder _ _ _ Col_B_M_A) as (_ & _ & Col_A_B_M & _ & _).

	assert (~ eq M C) as neq_M_C.
	{
		intros eq_M_C.
		assert (Col A B C) as Col_A_B_C by (rewrite <- eq_M_C; exact Col_A_B_M).

		contradict Col_A_B_C.
		pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.
		exact n_Col_A_B_C.
	}

	pose proof (axiom_circle_center_radius _ _ _ _ _ CI_K_C_CE OnCirc_P_K) as Cong_CP_CE.
	pose proof (axiom_circle_center_radius _ _ _ _ _ CI_K_C_CE OnCirc_Q_K) as Cong_CQ_CE.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_CQ_CE) as Cong_CE_CQ.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_CP_CE Cong_CE_CQ) as Cong_CP_CQ.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_CP_CQ) as (Cong_PC_QC & _ & _).

	pose proof (lemma_congruenceflip _ _ _ _ Cong_MP_MQ) as (Cong_PM_QM & _ & _).

	pose proof (
		lemma_s_right_triangle _ _ _ _ BetS_P_M_Q Cong_PM_QM Cong_PC_QC neq_M_C
	) as RightTriangle_PMC.

	assert (eq M M) as eq_M_M by (reflexivity).
	assert (Col C M M) as Col_C_M_M by (unfold Col; one_of_disjunct eq_M_M).

	pose proof (
		lemma_s_perp_at
		_ _ _ _ _ _
		Col_C_M_M
		Col_A_B_M
		Col_A_B_P
		RightTriangle_PMC
	) as Perp_at_CM_AB_M.

	exists M.
	exact Perp_at_CM_AB_M.
Qed.

End Euclid.
