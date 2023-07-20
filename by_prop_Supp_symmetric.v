Require Import ProofCheckingEuclid.by_def_Supp.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_Supp_symmetric :
	forall A B C D E,
	Supp A B C E D ->
	Supp D B E C A.
Proof.
	intros A B C D E.
	intros Supp_ABC_EBD.

	destruct Supp_ABC_EBD as (OnRay_BC_E & BetS_A_B_D).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_D) as BetS_D_B_A.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_BC_E) as OnRay_BE_C.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_BE_C BetS_D_B_A) as Supp_DBE_CBA.

	exact Supp_DBE_CBA.
Qed.

End Euclid.
