Require Import ProofCheckingEuclid.by_prop_OnRay_assert.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_OnRay_from_BetS_A_B_E :
	forall A B E,
	BetS A B E ->
	neq A B ->
	OnRay A B E.
Proof.
	intros A B E.
	intros BetS_A_B_E.
	intros neq_A_B.

	assert (BetS A E B \/ eq E B \/ BetS A B E) as BetS_A_E_B_or_eq_E_B_or_BetS_A_B_E.
	right.
	right.
	exact BetS_A_B_E.

	pose proof (by_prop_OnRay_assert _ _ _ BetS_A_E_B_or_eq_E_B_or_BetS_A_B_E neq_A_B) as OnRay_AB_E.
	exact OnRay_AB_E.
Qed.

End Euclid.
