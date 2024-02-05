Require Import ProofCheckingEuclid.by_def_SameSide.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_SameSide_flip :
	forall A B P Q,
	SameSide P Q A B ->
	SameSide P Q B A.
Proof.
	intros A B P Q.
	intros SameSide_P_Q_AB.


	destruct SameSide_P_Q_AB as (p & q & r & Col_A_B_p & Col_A_B_q & BetS_P_p_r & BetS_Q_q_r & nCol_A_B_P & nCol_A_B_Q).

	pose proof (by_prop_Col_order _ _ _ Col_A_B_p) as (Col_B_A_p & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_A_B_q) as (Col_B_A_q & _ & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_P) as (nCol_B_A_P & _ & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_Q) as (nCol_B_A_Q & _ & _ & _ & _).

	pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_B_A_p Col_B_A_q BetS_P_p_r BetS_Q_q_r nCol_B_A_P nCol_B_A_Q) as SameSide_P_Q_BA.

	exact SameSide_P_Q_BA.
Qed.

End Euclid.
