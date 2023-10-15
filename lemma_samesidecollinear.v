Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_SameSide.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_samesidecollinear :
	forall A B C P Q,
	SameSide P Q A B ->
	Col A B C ->
	neq A C ->
	SameSide P Q A C.
Proof.
	intros A B C P Q.
	intros SameSide_P_Q_AB.
	intros Col_A_B_C.
	intros neq_A_C.

	destruct SameSide_P_Q_AB as (p & q & r & Col_A_B_p & Col_A_B_q & BetS_P_p_r & BetS_Q_q_r & nCol_A_B_P & nCol_A_B_Q).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_P) as (neq_A_B & _ & _ & _ & _ & _).
	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C A B A eq_A_A) as Col_A_B_A.
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_B_P Col_A_B_A Col_A_B_C neq_A_C) as nCol_A_C_P.
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_B_Q Col_A_B_A Col_A_B_C neq_A_C) as nCol_A_C_Q.
	pose proof (by_prop_Col_order _ _ _ Col_A_B_p) as (Col_B_A_p & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_A_B_C) as (Col_B_A_C & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_A_C Col_B_A_p neq_B_A) as Col_A_C_p.
	pose proof (by_prop_Col_order _ _ _ Col_A_B_q) as (Col_B_A_q & _ & _ & _ & _).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_A_C Col_B_A_q neq_B_A) as Col_A_C_q.
	pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_A_C_p Col_A_C_q BetS_P_p_r BetS_Q_q_r nCol_A_C_P nCol_A_C_Q) as SameSide_P_Q_AC.

	exact SameSide_P_Q_AC.
Qed.

End Euclid.
