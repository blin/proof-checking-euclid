Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

(* TODO: rename to lemma_onray_neq_A_C *)
Lemma by_prop_OnRay_neq_A_C :
	forall A B C,
	OnRay A B C ->
	neq A C.
Proof.
	intros A B C.
	intros OnRay_AB_C.

	destruct OnRay_AB_C as (J & BetS_J_A_C & _).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_J_A_C) as (neq_A_C & _).

	exact neq_A_C.
Qed.

End Euclid.
