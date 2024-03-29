Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_layoffunique.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_Lt_between :
	forall A B C,
	Lt A B A C ->
	OnRay A B C ->
	BetS A B C.
Proof.
	intros A B C.
	intros Lt_AB_AC.
	intros OnRay_AB_C.

	destruct Lt_AB_AC as (M & BetS_A_M_C & Cong_AM_AB).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_M_C) as (_ & neq_A_M & _).

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_A_M_C neq_A_M) as OnRay_AM_C.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_AM_C) as OnRay_AC_M.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_AB_C) as OnRay_AC_B.

	pose proof (lemma_layoffunique _ _ _ _ OnRay_AC_M OnRay_AC_B Cong_AM_AB) as eq_M_B.

	assert (BetS A B C) as BetS_A_B_C by (rewrite <- eq_M_B; exact BetS_A_M_C).

	exact BetS_A_B_C.
Qed.

End Euclid.
