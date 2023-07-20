Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_SameSide.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_SameSide_reflexive :
	forall A B P,
	nCol A B P ->
	SameSide P P A B.
Proof.
	intros A B P.
	intros nCol_A_B_P.

	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C A B A eq_A_A) as Col_A_B_A.

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_P) as (_ & _ & neq_A_P & _ & _ & neq_P_A).

	pose proof (postulate_Euclid2 _ _ neq_P_A) as (C & BetS_P_A_C).

	pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_A_B_A Col_A_B_A BetS_P_A_C BetS_P_A_C nCol_A_B_P nCol_A_B_P) as SameSide_P_P_AB.

	exact SameSide_P_P_AB.
Qed.

End Euclid.
