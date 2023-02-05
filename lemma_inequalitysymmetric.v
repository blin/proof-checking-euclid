Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_inequalitysymmetric :
	forall A B,
	neq A B ->
	neq B A.
Proof.
	intros A B.
	intros neq_A_B.
	intros eq_B_A.

	pose proof (lemma_equalitysymmetric _ _ eq_B_A) as eq_A_B.
	contradict eq_A_B.
	exact neq_A_B.
Qed.

End Euclid.
