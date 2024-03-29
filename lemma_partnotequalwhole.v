Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_extensionunique.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_partnotequalwhole :
	forall A B C,
	BetS A B C ->
	~ Cong A B A C.
Proof.
	intros A B C.
	intros BetS_A_B_C.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_B_C) as (neq_B_C & neq_A_B & _).
	apply by_prop_neq_symmetric in neq_A_B as neq_B_A.
	pose proof (postulate_Euclid2 _ _ neq_B_A) as (D & BetS_B_A_D).
	apply axiom_betweennesssymmetry in BetS_B_A_D as BetS_D_A_B.
	pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_D_A_B BetS_A_B_C) as BetS_D_A_C.
	assert (~ Cong A B A C) as nCong_AB_AC.
	{
		intro Cong_AB_AC.

		pose proof (lemma_extensionunique _ _ _ _ BetS_D_A_B BetS_D_A_C Cong_AB_AC) as eq_B_C.

		contradict eq_B_C.
		exact neq_B_C.
	}
	exact nCong_AB_AC.
Qed.

End Euclid.
