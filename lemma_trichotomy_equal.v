Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_outerconnectivity.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_trichotomy_equal :
	forall A B C D,
	~ Lt A B C D ->
	~ Lt C D A B ->
	neq A B ->
	neq C D ->
	Cong A B C D.
Proof.
	intros A B C D.
	intros n_Lt_AB_CD.
	intros n_Lt_CD_AB.
	intros neq_A_B.
	intros neq_C_D.

	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.

	pose proof (lemma_extension _ _ _ _ neq_B_A neq_A_B) as (P & BetS_B_A_P & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_P) as BetS_P_A_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_A_P) as (neq_A_P & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_A_P) as neq_P_A.

	pose proof (lemma_extension _ _ _ _ neq_P_A neq_C_D) as (E & BetS_P_A_E & Cong_AE_CD).

	pose proof (cn_congruencereflexive A B) as Cong_AB_AB.

	assert (~ BetS A B E) as nBetS_A_B_E.
	{
		intros BetS_A_B_E.

		pose proof (by_def_Lt _ _ _ _ _ BetS_A_B_E Cong_AB_AB) as Lt_AB_AE.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_AB_AE Cong_AE_CD) as Lt_AB_CD.

		contradict Lt_AB_CD.
		exact n_Lt_AB_CD.
	}

	assert (~ BetS A E B) as nBetS_A_E_B.
	{
		intros BetS_A_E_B.

		pose proof (by_def_Lt _ _ _ _ _ BetS_A_E_B Cong_AE_CD) as Lt_CD_AB.
		contradict Lt_CD_AB.

		exact n_Lt_CD_AB.
	}

	pose proof (lemma_outerconnectivity _ _ _ _ BetS_P_A_E BetS_P_A_B nBetS_A_E_B nBetS_A_B_E) as eq_E_B.

	assert (Cong A B A E) as Cong_AB_AE by (rewrite eq_E_B; exact Cong_AB_AB).

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AB_AE Cong_AE_CD) as Cong_AB_CD.

	exact Cong_AB_CD.

Qed.

End Euclid.
