Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_collinearright.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_right_triangle_CBA_n_ACB.
Require Import ProofCheckingEuclid.lemma_right_triangle_NC.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.by_def_RightTriangle.
Require Import ProofCheckingEuclid.lemma_sameside_onray_EFAC_BFG_EGAC.
Require Import ProofCheckingEuclid.lemma_samesidereflexive.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.
Require Import ProofCheckingEuclid.proposition_10.
Require Import ProofCheckingEuclid.proposition_12.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_notperp :
	forall A B C P,
	BetS A C B ->
	nCol A B P ->
	exists X, nCol A B X /\ SameSide X P A B /\ ~ RightTriangle A C X.
Proof.
	intros A B C P.
	intros BetS_A_C_B.
	intros nCol_A_B_P.


	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_C_B) as Col_A_C_B.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_C_B) as (neq_C_B & neq_A_C & neq_A_B).
	pose proof (lemma_collinearorder _ _ _ Col_A_C_B) as (Col_C_A_B & Col_C_B_A & Col_B_A_C & Col_A_B_C & Col_B_C_A).

	pose proof (lemma_inequalitysymmetric _ _ neq_C_B) as neq_B_C.
	pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.

	pose proof (lemma_samesidereflexive _ _ _ nCol_A_B_P) as SameSide_P_P_AB.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_P) as n_Col_A_B_P.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_P) as (_ & neq_B_P & neq_A_P & _ & neq_P_B & neq_P_A).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_P) as (nCol_B_A_P & nCol_B_P_A & nCol_P_A_B & nCol_A_P_B & nCol_P_B_A).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_B_P Col_A_B_C neq_A_C) as nCol_A_C_P.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_C_P) as (_ & neq_C_P & _ & _ & neq_P_C & _).

	pose proof (lemma_extension _ _ _ _ neq_B_C neq_C_P) as (Q & BetS_B_C_Q & Cong_CQ_CP).

	pose proof (lemma_betweennotequal _ _ _ BetS_B_C_Q) as (neq_C_Q & _ & neq_B_Q).
	pose proof (lemma_inequalitysymmetric _ _ neq_C_Q) as neq_Q_C.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_B_C_Q) as Col_B_C_Q.
	pose proof (lemma_collinearorder _ _ _ Col_B_C_Q) as (Col_C_B_Q & Col_C_Q_B & Col_Q_B_C & Col_B_Q_C & Col_Q_C_B).

	pose proof (lemma_congruenceflip _ _ _ _ Cong_CQ_CP) as (Cong_QC_PC & _ & _).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_B_A Col_C_B_Q neq_C_B) as Col_B_A_Q.
	pose proof (lemma_collinearorder _ _ _ Col_B_A_Q) as (Col_A_B_Q & Col_A_Q_B & Col_Q_B_A & Col_B_Q_A & Col_Q_A_B).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_A_P Col_B_A_Q neq_B_Q) as nCol_B_Q_P.
	pose proof (lemma_NCorder _ _ _ nCol_B_Q_P) as (nCol_Q_B_P & nCol_Q_P_B & nCol_P_B_Q & nCol_B_P_Q & nCol_P_Q_B).
	pose proof (lemma_NCdistinct _ _ _ nCol_B_Q_P) as (_ & neq_Q_P & _ & _ & neq_P_Q & _).

	pose proof (proposition_10 _ _ neq_P_Q) as (M & BetS_P_M_Q & Cong_MP_MQ).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_M_Q) as BetS_Q_M_P.
	pose proof (lemma_betweennotequal _ _ _ BetS_P_M_Q) as (neq_M_Q & neq_P_M & _).

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_P_M_Q) as Col_P_M_Q.
	pose proof (lemma_collinearorder _ _ _ Col_P_M_Q) as (Col_M_P_Q & Col_M_Q_P & Col_Q_P_M & Col_P_Q_M & Col_Q_M_P).

	pose proof (lemma_doublereverse _ _ _ _ Cong_MP_MQ) as (Cong_QM_PM & _).

	pose proof (lemma_s_onray_assert_bets_AEB _ _ _ BetS_Q_M_P neq_Q_P) as OnRay_QP_M.

	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_P_P_AB Col_A_Q_B OnRay_QP_M) as SameSide_P_M_AB.
	pose proof (lemma_samesidesymmetric _ _ _ _ SameSide_P_M_AB) as (SameSide_M_P_AB & _ & _).


	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_P_Q_B Col_P_Q_M neq_P_M) as nCol_P_M_B.
	pose proof (lemma_NCorder _ _ _ nCol_P_M_B) as (nCol_M_P_B & nCol_M_B_P & nCol_B_P_M & nCol_P_B_M & nCol_B_M_P).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_M_P_B Col_M_P_Q neq_M_Q) as nCol_M_Q_B.
	pose proof (lemma_NCorder _ _ _ nCol_M_Q_B) as (nCol_Q_M_B & nCol_Q_B_M & nCol_B_M_Q & nCol_M_B_Q & nCol_B_Q_M).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_Q_M Col_B_Q_C neq_B_C) as nCol_B_C_M.
	pose proof (lemma_NCorder _ _ _ nCol_B_C_M) as (nCol_C_B_M & nCol_C_M_B & nCol_M_B_C & nCol_B_M_C & nCol_M_C_B).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_C_M Col_B_C_A neq_B_A) as nCol_B_A_M.
	pose proof (lemma_NCorder _ _ _ nCol_B_A_M) as (nCol_A_B_M & nCol_A_M_B & nCol_M_B_A & nCol_B_M_A & nCol_M_A_B).

	pose proof (proposition_12 _ _ _ nCol_A_B_M) as (R & Perp_at_M_R_A_B_R).

	destruct Perp_at_M_R_A_B_R as (E & _ & Col_A_B_R & Col_A_B_E & RightTriangle_ERM).

	pose proof (lemma_collinearorder _ _ _ Col_A_B_R) as (Col_B_A_R & _ & _ & _ & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_C Col_A_B_R neq_A_B) as Col_B_C_R.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_C Col_A_B_E neq_A_B) as Col_B_C_E.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_E Col_A_B_R neq_A_B) as Col_B_E_R.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_C Col_B_A_R neq_B_A) as Col_A_C_R.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_C_R Col_B_C_E neq_B_C) as Col_C_R_E.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_E Col_A_B_Q neq_A_B) as Col_B_E_Q.
	pose proof (lemma_collinearorder _ _ _ Col_C_R_E) as (_ & _ & _ & _ & Col_E_R_C).

	assert (~ RightTriangle A C M) as n_RightTriangle_ACM.
	{
		intro RightTriangle_ACM.

		pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_ACM) as nCol_A_C_M.
		pose proof (lemma_NCdistinct _ _ _ nCol_A_C_M) as (_ & neq_C_M & neq_A_M & neq_C_A & neq_M_C & neq_M_A).

		pose proof (by_def_RightTriangle _ _ _ _ BetS_Q_M_P Cong_QM_PM Cong_QC_PC neq_M_C) as RightTriangle_QMC.

		assert (~ neq R C) as n_neq_R_C.
		{
			intro neq_R_C.

			pose proof (lemma_inequalitysymmetric _ _ neq_R_C) as neq_C_R.

			pose proof (lemma_collinearright _ _ _ _ RightTriangle_ACM Col_A_C_R neq_R_C) as RightTriangle_RCM.
			pose proof (lemma_right_triangle_CBA_n_ACB _ _ _ RightTriangle_RCM) as n_RightTriangle_MRC.

			pose proof (lemma_collinearright _ _ _ _ RightTriangle_ERM Col_E_R_C neq_C_R) as RightTriangle_CRM.
			pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_CRM) as RightTriangle_MRC.

			contradict RightTriangle_MRC.
			exact n_RightTriangle_MRC.
		}
		assert (eq_R_C := n_neq_R_C).
		apply Classical_Prop.NNPP in eq_R_C.

		assert (neq Q R) as neq_Q_R by (rewrite eq_R_C; exact neq_Q_C).

		assert (~ neq B E) as n_neq_B_E.
		{
			intro neq_B_E.

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_E_R Col_B_E_Q neq_B_E) as Col_E_R_Q.
			pose proof (lemma_collinearright _ _ _ _ RightTriangle_ERM Col_E_R_Q neq_Q_R) as RightTriangle_QRM.

			assert (RightTriangle Q C M) as RightTriangle_QCM by (rewrite <- eq_R_C; exact RightTriangle_QRM).

			pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_QCM) as RightTriangle_MCQ.
			pose proof (lemma_right_triangle_CBA_n_ACB _ _ _ RightTriangle_MCQ) as n_RightTriangle_QMC.

			contradict RightTriangle_QMC.
			exact n_RightTriangle_QMC.
		}
		assert (eq_B_E := n_neq_B_E).
		apply Classical_Prop.NNPP in eq_B_E.

		assert (Col A E R) as Col_A_E_R by (rewrite <- eq_B_E; exact Col_A_B_R).
		assert (Col A E Q) as Col_A_E_Q by (rewrite <- eq_B_E; exact Col_A_B_Q).
		assert (neq A E) as neq_A_E by (rewrite <- eq_B_E; exact neq_A_B).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_E_R Col_A_E_Q neq_A_E) as Col_E_R_Q.
		pose proof (lemma_collinearright _ _ _ _ RightTriangle_ERM Col_E_R_Q neq_Q_R) as RightTriangle_QRM.

		assert (RightTriangle Q C M) as RightTriangle_QCM by (rewrite <- eq_R_C; exact RightTriangle_QRM).

		pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_QCM) as RightTriangle_MCQ.
		pose proof (lemma_right_triangle_CBA_n_ACB _ _ _ RightTriangle_MCQ) as n_RightTriangle_QMC.

		contradict RightTriangle_QMC.
		exact n_RightTriangle_QMC.
	}

	exists M.
	split.
	exact nCol_A_B_M.
	split.
	exact SameSide_M_P_AB.
	exact n_RightTriangle_ACM.
Qed.

End Euclid.
