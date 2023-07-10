Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_ss.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_samesidereflexive :
	forall A B P,
	nCol A B P ->
	SameSide P P A B.
Proof.
	intros A B P.
	intros nCol_A_B_P.

	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (lemma_s_col_eq_A_C A B A eq_A_A) as Col_A_B_A.

	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_P) as (_ & _ & neq_A_P & _ & _ & neq_P_A).

	pose proof (postulate_Euclid2 _ _ neq_P_A) as (C & BetS_P_A_C).

	pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_A_B_A Col_A_B_A BetS_P_A_C BetS_P_A_C nCol_A_B_P nCol_A_B_P) as SameSide_P_P_AB.

	exact SameSide_P_P_AB.
Qed.

End Euclid.
