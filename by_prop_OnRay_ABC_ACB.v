Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_prop_OnRay_neq_A_C.
Require Import ProofCheckingEuclid.by_prop_OnRay_orderofpoints_any.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_OnRay_ABC_ACB :
	forall A B C,
	OnRay A B C ->
	OnRay A C B.
Proof.
	intros A B C.
	intros OnRay_AB_C.

	pose proof (by_prop_OnRay_neq_A_C _ _ _ OnRay_AB_C) as neq_A_C.
	pose proof (
		by_prop_OnRay_orderofpoints_any _ _ _ OnRay_AB_C
	) as BetS_A_C_B_or_eq_B_C_or_BetS_A_B_C.

	assert (OnRay A C B) as OnRay_AC_B.
	{
		destruct BetS_A_C_B_or_eq_B_C_or_BetS_A_B_C as [BetS_A_C_B | [eq_B_C | BetS_A_B_C]].
		{
			(* case BetS_A_C_B *)
			pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_A_C_B neq_A_C) as OnRay_AC_B.
			exact OnRay_AC_B.
		}
		{
			(* case eq_B_C *)
			epose proof (by_def_OnRay_from_neq_A_B _ _ neq_A_C) as OnRay_AC_C.
			assert (OnRay A C B) as OnRay_AC_B by (rewrite eq_B_C; exact OnRay_AC_C).
			exact OnRay_AC_B.
		}
		{
			(* case BetS_A_B_C *)
			pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_A_B_C neq_A_C) as OnRay_AC_B.
			exact OnRay_AC_B.
		}
	}
	exact OnRay_AC_B.
Qed.

End Euclid.
