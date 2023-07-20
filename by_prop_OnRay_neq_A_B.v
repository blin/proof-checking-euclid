Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma by_prop_OnRay_neq_A_B :
	forall A B C,
	OnRay A B C ->
	neq A B.
Proof.
	intros A B C.
	intros OnRay_AB_C.

	destruct OnRay_AB_C as (J & _ & BetS_J_A_B).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_J_A_B) as (neq_A_B & _).

	exact neq_A_B.
Qed.

End Euclid.
