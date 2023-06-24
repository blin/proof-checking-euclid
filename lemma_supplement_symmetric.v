Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_s_supp.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_supplement_symmetric :
	forall A B C D E,
	Supp A B C E D ->
	Supp D B E C A.
Proof.
	intros A B C D E.
	intros Supp_A_B_C_E_D.

	destruct Supp_A_B_C_E_D as (OnRay_B_C_E & BetS_A_B_D).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_D) as BetS_D_B_A.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_B_C_E) as OnRay_B_E_C.
	pose proof (lemma_s_supp _ _ _ _ _ OnRay_B_E_C BetS_D_B_A) as Supp_D_B_E_C_A.

	exact Supp_D_B_E_C_A.
Qed.

End Euclid.
