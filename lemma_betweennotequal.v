Require Import Coq.Setoids.Setoid.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.


Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_betweennotequal :
	forall A B C,
	BetS A B C ->
	neq B C /\ neq A B /\ neq A C.
Proof.
	intros A B C.
	intros BetS_A_B_C.

	assert (~ eq B C) as neq_B_C.
	{
		intro eq_B_C.
		assert (BetS A C B) as BetS_A_C_B.
		replace B with C at 1.
		replace C with B at 1.
		exact BetS_A_B_C.
		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_B_C BetS_A_C_B) as BetS_B_C_B.
		pose proof (axiom_betweennessidentity B C) as nBetS_B_C_B.
		contradiction.
	}

	assert (~ eq A B) as neq_A_B.
	{
		intro eq_A_B.
		assert (BetS B A C) as BetS_B_A_C.
		replace A with B at 1.
		replace B with A at 1.
		exact BetS_A_B_C.
		pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_A_B_C BetS_B_A_C) as BetS_A_B_A.
		pose proof (axiom_betweennessidentity A B) as nBetS_A_B_A.
		contradiction.
	}

	assert (~ eq A C) as neq_A_C.
	{
		intro eq_A_C.
		assert (BetS A B A) as BetS_A_B_A.
		replace A with C at 2.
		exact BetS_A_B_C.
		pose proof (axiom_betweennessidentity A B) as nBetS_A_B_A.
		contradiction.
	}

	repeat split.
	exact neq_B_C.
	exact neq_A_B.
	exact neq_A_C.
Qed.

End Euclid.


