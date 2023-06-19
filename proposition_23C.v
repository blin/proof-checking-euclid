Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_ss.
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

	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (lemma_s_col_eq_A_C A B A eq_A_A) as Col_A_B_A.

	pose proof (lemma_NCdistinct _ _ _ nCol_D_C_E) as (neq_D_C & neq_C_E & neq_D_E & neq_C_D & neq_E_C & neq_E_D).
	pose proof (lemma_NCorder _ _ _ nCol_D_C_E) as (nCol_C_D_E & nCol_C_E_D & nCol_E_D_C & nCol_D_E_C & nCol_E_C_D).

	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_P) as (_ & neq_B_P & neq_A_P & neq_B_A & neq_P_B & neq_P_A).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_P) as (nCol_B_A_P & nCol_B_P_A & nCol_P_A_B & nCol_A_P_B & nCol_P_B_A).


	pose proof (postulate_Euclid2 _ _ neq_P_A) as (Q & BetS_P_A_Q).

	pose proof (lemma_betweennotequal _ _ _ BetS_P_A_Q) as (neq_A_Q & _ & neq_P_Q).

	pose proof (lemma_s_col_BetS_A_B_C P A Q BetS_P_A_Q) as Col_P_A_Q.
	pose proof (lemma_collinearorder _ _ _ Col_P_A_Q) as (Col_A_P_Q & Col_A_Q_P & Col_Q_P_A & Col_P_Q_A & Col_Q_A_P).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_P_B Col_A_P_Q neq_A_Q) as nCol_A_Q_B.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_Q_B) as (_ & neq_Q_B & _ & neq_Q_A & neq_B_Q & _).
	pose proof (lemma_NCorder _ _ _ nCol_A_Q_B) as (nCol_Q_A_B & nCol_Q_B_A & nCol_B_A_Q & nCol_A_B_Q & nCol_B_Q_A).

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
