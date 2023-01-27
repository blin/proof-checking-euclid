Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_onray_assert.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_onray_assert_ABB :
	forall A B,
	neq A B ->
	OnRay A B B.
Proof.
	intros A B.
	intros neq_A_B.
	assert (eq B B) as eq_B_B by (reflexivity).

	assert (BetS A B B \/ eq B B \/ BetS A B B) as BetS_A_B_B_or_eq_B_B_or_BetS_A_B_B.
	one_of_disjunct eq_B_B.

	pose proof (lemma_onray_assert _ _ _ BetS_A_B_B_or_eq_B_B_or_BetS_A_B_B neq_A_B) as OnRay_AB_B.
	exact OnRay_AB_B.
Qed.

End Euclid.
