Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_onray_assert.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_onray_assert_bets_ABE :
	forall A B E,
	BetS A B E ->
	neq A B ->
	OnRay A B E.
Proof.
	intros A B E.
	intros BetS_A_B_E.
	intros neq_A_B.

	assert (BetS A E B \/ eq E B \/ BetS A B E) as BetS_A_E_B_or_eq_E_B_or_BetS_A_B_E.
	one_of_disjunct BetS_A_B_E.

	pose proof (lemma_onray_assert _ _ _ BetS_A_E_B_or_eq_E_B_or_BetS_A_B_E neq_A_B) as OnRay_AB_E.
	exact OnRay_AB_E.
Qed.

End Euclid.
