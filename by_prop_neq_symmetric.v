Require Import ProofCheckingEuclid.by_prop_eq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma by_prop_neq_symmetric :
	forall A B,
	neq A B ->
	neq B A.
Proof.
	intros A B.
	intros neq_A_B.
	intros eq_B_A.

	pose proof (by_prop_eq_symmetric _ _ eq_B_A) as eq_A_B.
	contradict eq_A_B.
	exact neq_A_B.
Qed.

End Euclid.
