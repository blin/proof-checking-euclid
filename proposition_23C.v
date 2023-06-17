Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
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
Require Import ProofCheckingEuclid.proposition_23B.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_23C :
	forall A B C D E P,
	neq A B ->
	nCol D C E ->
	nCol A B P ->
	exists X Y, OnRay A B Y /\ CongA X A Y D C E /\ SS X P A B.
Proof.
	intros A B C D E P.
	intros neq_A_B.
	intros nCol_D_C_E.
	intros nCol_A_B_P.

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_P) as n_Col_A_B_P.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_D_C_E) as n_Col_D_C_E.

	assert (~ eq P A) as n_eq_P_A.
	{
		intro eq_P_A.
		pose proof (lemma_equalitysymmetric _ _ eq_P_A) as eq_A_P.
		pose proof (lemma_s_col_eq_A_C A B P eq_A_P) as Col_A_B_P.
		contradict Col_A_B_P.
		exact n_Col_A_B_P.
	}
	assert (neq_P_A := n_eq_P_A).


	pose proof (lemma_extension P A P A neq_P_A neq_P_A) as (Q & BetS_P_A_Q & Cong_A_Q_P_A).
	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (lemma_s_col_eq_A_C A B A eq_A_A) as Col_A_B_A.

	assert (~ Col A B Q) as n_Col_A_B_Q.
	{
		intro Col_A_B_Q.
		pose proof (lemma_s_col_BetS_A_B_C P A Q BetS_P_A_Q) as Col_P_A_Q.
		pose proof (lemma_collinearorder _ _ _ Col_A_B_Q) as (_ & _ & Col_Q_A_B & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_P_A_Q) as (_ & _ & _ & _ & Col_Q_A_P).
		pose proof (lemma_betweennotequal _ _ _ BetS_P_A_Q) as (neq_A_Q & _ & _).
		pose proof (lemma_inequalitysymmetric _ _ neq_A_Q) as neq_Q_A.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_A_B Col_Q_A_P neq_Q_A) as Col_A_B_P.
		contradict Col_A_B_P.
		exact n_Col_A_B_P.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_B_Q) as nCol_A_B_Q.

	pose proof (proposition_23B _ _ _ _ _ _ neq_A_B nCol_D_C_E nCol_A_B_Q) as (F & G & OnRay_A_B_G & CongA_F_A_G_D_C_E & OS_F_A_B_Q).

	destruct OS_F_A_B_Q as (J & BetS_F_J_Q & Col_A_B_J & nCol_A_B_F).
	pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_A_B_J Col_A_B_A BetS_F_J_Q BetS_P_A_Q nCol_A_B_F nCol_A_B_P) as SS_F_P_A_B.
	exists F, G.
	split.
	exact OnRay_A_B_G.
	split.
	exact CongA_F_A_G_D_C_E.
	exact SS_F_P_A_B.
Qed.

End Euclid.
