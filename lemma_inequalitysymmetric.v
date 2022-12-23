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
	unfold neq.
	intros neq_A_B.
	intros eq_B_A.
	apply lemma_equalitysymmetric in eq_B_A.
	contradiction.
Qed.

End Euclid.
