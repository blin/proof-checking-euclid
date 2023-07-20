Require Import ProofCheckingEuclid.by_prop_eq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_tactics.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma by_prop_Col_ABC_BCA :
	forall A B C,
	Col A B C ->
	Col B C A.
Proof.
	intros A B C.
	intros Col_A_B_C.

	unfold Col.

	unfold Col in Col_A_B_C.
	destruct Col_A_B_C as [eq_A_B | [eq_A_C | [eq_B_C | [BetS_B_A_C | [BetS_A_B_C | BetS_A_C_B]]]]].
	{
		(* case eq_A_B *)
		pose proof (by_prop_eq_symmetric _ _ eq_A_B) as eq_B_A.
		one_of_disjunct eq_B_A.
	}
	{
		(* case eq_A_C *)
		pose proof (by_prop_eq_symmetric _ _ eq_A_C) as eq_C_A.
		one_of_disjunct eq_C_A.
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
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_C) as BetS_C_B_A.
		one_of_disjunct BetS_C_B_A.
	}
	{
		(* case BetS_A_C_B *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_B) as BetS_B_C_A.
		one_of_disjunct BetS_B_C_A.
	}
Qed.

End Euclid.
