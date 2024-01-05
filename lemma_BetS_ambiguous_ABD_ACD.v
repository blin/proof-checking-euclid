Require Import Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_BetS_ambiguous_ABD_ACD :
	forall A B C D,
	BetS A B D ->
	BetS A C D ->
	(BetS A B C \/ eq B C \/ BetS A C B).
Proof.
	intros A B C D.
	intros BetS_A_B_D.
	intros BetS_A_C_D.

	assert (~ ~ (BetS A B C \/ eq B C \/ BetS A C B)) as n_n_BetS_A_B_C_or_eq_B_C_or_BetS_A_C_B.
	{
		intro n_BetS_A_B_C_or_eq_B_C_or_BetS_A_C_B.

		apply Classical_Prop.not_or_and in n_BetS_A_B_C_or_eq_B_C_or_BetS_A_C_B.
		destruct n_BetS_A_B_C_or_eq_B_C_or_BetS_A_C_B as (n_BetS_A_B_C & eq_B_C_or_n_BetS_A_C_B).
		apply Classical_Prop.not_or_and in eq_B_C_or_n_BetS_A_C_B.
		destruct eq_B_C_or_n_BetS_A_C_B as (neq_B_C & n_BetS_A_C_B).

		pose proof (axiom_connectivity _ _ _ _ BetS_A_B_D BetS_A_C_D n_BetS_A_B_C n_BetS_A_C_B) as eq_B_C.

		contradict eq_B_C.
		exact neq_B_C.
	}
	assert (BetS_A_B_C_or_eq_B_C_or_BetS_A_C_B := n_n_BetS_A_B_C_or_eq_B_C_or_BetS_A_C_B).
	apply Classical_Prop.NNPP in BetS_A_B_C_or_eq_B_C_or_BetS_A_C_B.

	exact BetS_A_B_C_or_eq_B_C_or_BetS_A_C_B.
Qed.

End Euclid.
