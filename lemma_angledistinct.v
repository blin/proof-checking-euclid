Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_angledistinct :
	forall A B C a b c,
	CongA A B C a b c ->
	neq A B /\ neq B C /\ neq A C /\ neq a b /\ neq b c /\ neq a c.
Proof.
	intros A B C a b c.
	intros CongA_ABC_abc.

	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_ABC_abc) as CongA_abc_ABC.
	destruct CongA_ABC_abc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nCol_A_B_C).
	destruct CongA_abc_ABC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nCol_a_b_c).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & _).
	pose proof (lemma_NCdistinct _ _ _ nCol_a_b_c) as (neq_a_b & neq_b_c & neq_a_c & _).

	repeat split.

	exact neq_A_B.
	exact neq_B_C.
	exact neq_A_C.
	exact neq_a_b.
	exact neq_b_c.
	exact neq_a_c.
Qed.

End Euclid.
