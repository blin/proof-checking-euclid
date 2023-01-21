Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_collinear_ABC_BAC :
	forall A B C,
	Col A B C ->
	Col B A C.
Proof.
	intros A B C.
	intros Col_A_B_C.

	unfold Col.

	unfold Col in Col_A_B_C.
	destruct Col_A_B_C as [eq_A_B | [eq_A_C | [eq_B_C | [BetS_B_A_C | [BetS_A_B_C | BetS_A_C_B]]]]].
	{
		(* case eq_A_B *)
		pose proof (lemma_equalitysymmetric _ _ eq_A_B) as eq_B_A.
		one_of_disjunct eq_B_A.
	}
	{
		(* case eq_A_C *)
		one_of_disjunct eq_A_C.
	}
	{
		(* case eq_B_C *)
		one_of_disjunct eq_B_C.
	}
	{
		(* case BetS_B_A_C *)
		one_of_disjunct BetS_B_A_C.
	}
	{
		(* case BetS_A_B_C *)
		one_of_disjunct BetS_A_B_C.
	}
	{
		(* case BetS_A_C_B *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_B) as BetS_B_C_A.
		one_of_disjunct BetS_B_C_A.
	}
Qed.

End Euclid.
