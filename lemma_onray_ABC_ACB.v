Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_onray_orderofpoints_any.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_onray_strict.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_onray_ABC_ACB :
	forall A B C,
	OnRay A B C ->
	OnRay A C B.
Proof.
	intros A B C.
	intros OnRay_AB_C.

	pose proof (
		lemma_onray_orderofpoints_any _ _ _ OnRay_AB_C
	) as BetS_A_C_B_or_eq_B_C_or_BetS_A_B_C.

	assert (BetS A B C \/ eq B C \/ BetS A C B) as BetS_A_B_C_or_eq_B_C_or_BetS_A_C_B.
	{
		destruct BetS_A_C_B_or_eq_B_C_or_BetS_A_B_C as [BetS_A_C_B | [eq_B_C | BetS_A_B_C]].
		{
			(* case BetS_A_C_B *)
			one_of_disjunct BetS_A_C_B.
		}
		{
			(* case eq_B_C *)
			one_of_disjunct eq_B_C.
		}
		{
			(* case BetS_A_B_C *)
			one_of_disjunct BetS_A_B_C.
		}
	}
	pose proof (lemma_onray_strict _ _ _ OnRay_AB_C) as neq_A_C.
	pose proof (lemma_onray_assert _ _ _ BetS_A_B_C_or_eq_B_C_or_BetS_A_C_B neq_A_C) as OnRay_AC_B.
	exact OnRay_AC_B.
Qed.

End Euclid.
