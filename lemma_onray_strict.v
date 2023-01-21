Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennotequal.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_onray_strict :
	forall A B C,
	OnRay A B C ->
	neq A C.
Proof.
	intros A B C.
	intros OnRay_AB_C.

	destruct OnRay_AB_C as (J & BetS_J_A_C & _).

	pose proof (lemma_betweennotequal _ _ _ BetS_J_A_C) as (neq_A_C & _).

	exact neq_A_C.
Qed.

End Euclid.
