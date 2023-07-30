Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_prop_eq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma by_prop_Col_ABC_BAC :
	forall A B C,
	Col A B C ->
	Col B A C.
Proof.
	intros A B C.
	intros Col_A_B_C.

	unfold Col in Col_A_B_C.
	destruct Col_A_B_C as [eq_A_B | [eq_A_C | [eq_B_C | [BetS_B_A_C | [BetS_A_B_C | BetS_A_C_B]]]]].
	{
		(* case eq_A_B *)
		pose proof (by_prop_eq_symmetric _ _ eq_A_B) as eq_B_A.
		pose proof (by_def_Col_from_eq_A_B B A C eq_B_A) as Col_B_A_C.
		exact Col_B_A_C.
	}
	{
		(* case eq_A_C *)
		pose proof (by_def_Col_from_eq_B_C B A C eq_A_C) as Col_B_A_C.
		exact Col_B_A_C.
	}
	{
		(* case eq_B_C *)
		pose proof (by_def_Col_from_eq_A_C B A C eq_B_C) as Col_B_A_C.
		exact Col_B_A_C.
	}
	{
		(* case BetS_B_A_C *)
		pose proof (by_def_Col_from_BetS_A_B_C B A C BetS_B_A_C) as Col_B_A_C.
		exact Col_B_A_C.
	}
	{
		(* case BetS_A_B_C *)
		pose proof (by_def_Col_from_BetS_B_A_C B A C BetS_A_B_C) as Col_B_A_C.
		exact Col_B_A_C.
	}
	{
		(* case BetS_A_C_B *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_B) as BetS_B_C_A.
		pose proof (by_def_Col_from_BetS_A_C_B B A C BetS_B_C_A) as Col_B_A_C.
		exact Col_B_A_C.
	}
Qed.

End Euclid.
