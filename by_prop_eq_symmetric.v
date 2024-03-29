Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma by_prop_eq_symmetric :
	forall A B,
	eq B A ->
	eq A B.
Proof.
	intros A B.
	intros eq_B_A.
	symmetry.
	exact eq_B_A.
Qed.

End Euclid.
