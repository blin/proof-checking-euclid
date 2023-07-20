Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_OnRay.
Require Import ProofCheckingEuclid.by_prop_eq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_outerconnectivity.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.


Lemma by_prop_OnRay_shared_initial_point :
	forall B C D V,
	OnRay B C D ->
	OnRay B C V ->
	OnRay B D V.
Proof.
	intros B C D V.
	intros OnRay_BC_D.
	intros OnRay_BC_V.

	destruct OnRay_BC_D as (E & BetS_E_B_D & BetS_E_B_C).
	destruct OnRay_BC_V as (H & BetS_H_B_V & BetS_H_B_C).

	assert (~ ~ BetS E B V) as BetS_E_B_V.
	{
		intros nBetS_E_B_V.

		assert (~ BetS B E H) as nBetS_B_E_H.
		{
			intros BetS_B_E_H.

			pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_E_H) as BetS_H_E_B.
			pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_H_E_B BetS_H_B_V) as BetS_E_B_V.

			contradict BetS_E_B_V.
			exact nBetS_E_B_V.
		}

		assert (~ BetS B H E) as nBetS_B_H_E.
		{
			intros BetS_B_H_E.

			pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_H_E) as BetS_E_H_B.
			pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_E_H_B BetS_H_B_V) as BetS_E_B_V.

			contradict BetS_E_B_V.
			exact nBetS_E_B_V.
		}

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_B_C) as BetS_C_B_E.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_B_C) as BetS_C_B_H.
		pose proof (lemma_outerconnectivity _ _ _ _ BetS_C_B_H BetS_C_B_E nBetS_B_H_E nBetS_B_E_H) as eq_H_E.

		pose proof (by_prop_eq_symmetric _ _ eq_H_E) as eq_E_H.
		assert (BetS E B V) as BetS_E_B_V by (rewrite eq_E_H; exact BetS_H_B_V).

		contradict BetS_E_B_V.
		exact nBetS_E_B_V.
	}
	apply Classical_Prop.NNPP in BetS_E_B_V.

	pose proof (by_def_OnRay _ _ _ _ BetS_E_B_D BetS_E_B_V) as OnRay_BD_V.
	exact OnRay_BD_V.
Qed.

End Euclid.
