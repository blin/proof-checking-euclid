Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_tactics.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_supporting_n_ncol_col :
	forall A B C,
	~ nCol A B C ->
	Col A B C.
Proof.
	intros A B C.
	intros Col_A_B_C.

	unfold nCol in Col_A_B_C.
	unfold neq in Col_A_B_C.

	apply Classical_Prop.not_and_or in Col_A_B_C.
	destruct Col_A_B_C as [eq_A_B | Col_A_B_C].
	{
		apply Classical_Prop.NNPP in eq_A_B.
		one_of_disjunct eq_A_B.
	}

	apply Classical_Prop.not_and_or in Col_A_B_C.
	destruct Col_A_B_C as [eq_A_C | Col_A_B_C].
	{
		apply Classical_Prop.NNPP in eq_A_C.
		one_of_disjunct eq_A_C.
	}

	apply Classical_Prop.not_and_or in Col_A_B_C.
	destruct Col_A_B_C as [eq_B_C | Col_A_B_C].
	{
		apply Classical_Prop.NNPP in eq_B_C.
		one_of_disjunct eq_B_C.
	}

	apply Classical_Prop.not_and_or in Col_A_B_C.
	destruct Col_A_B_C as [BetS_A_B_C | Col_A_B_C].
	{
		apply Classical_Prop.NNPP in BetS_A_B_C.
		one_of_disjunct BetS_A_B_C.
	}

	apply Classical_Prop.not_and_or in Col_A_B_C.
	destruct Col_A_B_C as [BetS_A_C_B | BetS_B_A_C].
	{
		apply Classical_Prop.NNPP in BetS_A_C_B.
		one_of_disjunct BetS_A_C_B.
	}

	apply Classical_Prop.NNPP in BetS_B_A_C.
	one_of_disjunct BetS_B_A_C.
Qed.

End Euclid.

