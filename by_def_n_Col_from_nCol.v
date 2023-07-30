Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_n_Col_from_nCol :
	forall A B C,
	nCol A B C ->
	~ Col A B C.
Proof.
	intros A B C.
	intros nCol_A_B_C.

	assert (~ Col A B C) as n_Col_a_b_c.
	{
		intros Col_A_B_C.

		unfold nCol in nCol_A_B_C.
		unfold Col in Col_A_B_C.
		destruct nCol_A_B_C as (
			neq_A_B & neq_A_C & neq_B_C & nBetS_A_B_C & nBetS_A_C_B & nBetS_B_A_C
		).
		destruct Col_A_B_C as [
			eq_A_B | [eq_A_C | [eq_B_C | [BetS_B_A_C | [BetS_A_B_C | BetS_A_C_B]]]]
		].

		contradict eq_A_B.
		exact neq_A_B.
		contradict eq_A_C .
		exact neq_A_C .
		contradict eq_B_C .
		exact neq_B_C .
		contradict BetS_B_A_C .
		exact nBetS_B_A_C .
		contradict BetS_A_B_C.
		exact nBetS_A_B_C.
		contradict BetS_A_C_B .
		exact nBetS_A_C_B .
	}
	exact n_Col_a_b_c.
Qed.

End Euclid.
