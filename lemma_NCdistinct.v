Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_NCdistinct :
	forall A B C,
	nCol A B C ->
	neq A B /\ neq B C /\ neq A C /\ neq B A /\ neq C B /\ neq C A.
Proof.
	intros A B C.
	intros nCol_A_B_C.
	destruct nCol_A_B_C as (neq_A_B & neq_A_C & neq_B_C & _).
	apply lemma_inequalitysymmetric in neq_A_B as neq_B_A.
	apply lemma_inequalitysymmetric in neq_B_C as neq_C_B.
	apply lemma_inequalitysymmetric in neq_A_C as neq_C_A.

	repeat split.
	exact neq_A_B.
	exact neq_B_C.
	exact neq_A_C.
	exact neq_B_A.
	exact neq_C_B.
	exact neq_C_A.
Qed.

End Euclid.
