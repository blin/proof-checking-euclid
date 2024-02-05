Require Import ProofCheckingEuclid.by_prop_OnRay_neq_A_C.
Require Import ProofCheckingEuclid.by_prop_OnRay_orderofpoints_any.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_OnRay_ABC_BAC_BetS_ACB :
	forall A B C,
	OnRay A B C ->
	OnRay B A C ->
	BetS A C B.
Proof.
	intros A B C.
	intros OnRay_AB_C.
	intros OnRay_BA_C.

	pose proof (by_prop_OnRay_neq_A_C _ _ _ OnRay_AB_C) as neq_A_C.
	pose proof (by_prop_OnRay_neq_A_C _ _ _ OnRay_BA_C) as neq_B_C.

	(* assert by cases *)
	assert (BetS A C B) as BetS_A_C_B.
	pose proof (by_prop_OnRay_orderofpoints_any _ _ _ OnRay_AB_C) as [BetS_A_C_B | [eq_B_C | BetS_A_B_C]].
	{
		(* case BetS_A_C_B *)
		exact BetS_A_C_B.
	}
	{
		(* case eq_B_C *)
		contradict eq_B_C.
		exact neq_B_C.
	}
	{
		(* case BetS_A_B_C *)

		(* assert by cases *)
		assert (BetS A C B) as BetS_A_C_B.

		pose proof (by_prop_OnRay_orderofpoints_any _ _ _ OnRay_BA_C) as [BetS_B_C_A | [eq_A_C | BetS_B_A_C]].
		{
			(* case BetS_B_C_A *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_C_A) as BetS_A_C_B.

			exact BetS_A_C_B.
		}
		{
			(* case eq_A_C *)
			contradict eq_A_C.
			exact neq_A_C.
		}
		{
			(* case BetS_B_A_C *)
			pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_A_B_C BetS_B_A_C) as BetS_A_B_A.
			pose proof (axiom_betweennessidentity A B) as n_BetS_A_B_A.

			contradict BetS_A_B_A.
			exact n_BetS_A_B_A.
		}

		exact BetS_A_C_B.
	}

	exact BetS_A_C_B.
Qed.

End Euclid.
