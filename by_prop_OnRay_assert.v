Require Import ProofCheckingEuclid.by_def_OnRay.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_OnRay_assert :
	forall A B E,
	(BetS A E B \/ eq E B \/ BetS A B E) -> neq A B ->
	OnRay A B E.
Proof.
	intros A B E.
	intros BetS_A_E_B_or_eq_E_B_or_BetS_A_B_E.
	intros neq_A_B.

	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (lemma_extension _ _ _ _ neq_B_A neq_A_B) as (J & BetS_B_A_J & Cong_AJ_AB).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_J) as BetS_J_A_B.

	destruct BetS_A_E_B_or_eq_E_B_or_BetS_A_B_E as [BetS_A_E_B | [eq_E_B | BetS_A_B_E]].
	{
		(* case BetS_A_E_B *)
		pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_J_A_B BetS_A_E_B) as BetS_J_A_E.
		pose proof (by_def_OnRay _ _ _ _ BetS_J_A_B BetS_J_A_E) as OnRay_AB_E.
		exact OnRay_AB_E.
	}
	{
		(* case eq_E_B *)
		assert (BetS J A E) as BetS_J_A_E by (rewrite eq_E_B; exact BetS_J_A_B).
		pose proof (by_def_OnRay _ _ _ _ BetS_J_A_B BetS_J_A_E) as OnRay_AB_E.
		exact OnRay_AB_E.
	}
	{
		(* case BetS_A_B_E *)
		pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_J_A_B BetS_A_B_E) as BetS_J_A_E.
		pose proof (by_def_OnRay _ _ _ _ BetS_J_A_B BetS_J_A_E) as OnRay_AB_E.
		exact OnRay_AB_E.
	}
Qed.

End Euclid.
