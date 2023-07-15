Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_betweenness.
Require Coq.Logic.Classical_Prop.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_onray_orderofpoints_any :
	forall A B P,
	OnRay A B P ->
	(BetS A P B \/ eq B P \/ BetS A B P).
Proof.
	intros A B P.
	intros OnRay_AB_P.

	assert (~ ~ (BetS A P B \/ eq B P \/ BetS A B P)) as BetS_A_P_B_or_eq_B_P_or_BetS_A_B_P.
	{
		intro n_BetS_A_P_B_or_eq_B_P_or_BetS_A_B_P.

		apply Classical_Prop.not_or_and in n_BetS_A_P_B_or_eq_B_P_or_BetS_A_B_P as (
			nBetS_A_P_B & n_eq_B_P_or_BetS_A_B_P
		).
		apply Classical_Prop.not_or_and in n_eq_B_P_or_BetS_A_B_P as (neq_B_P & nBetS_A_B_P).
		pose proof (lemma_inequalitysymmetric _ _ neq_B_P) as neq_P_B.
		pose proof (lemma_onray_betweenness _ _ _ OnRay_AB_P neq_P_B nBetS_A_P_B) as BetS_A_B_P.

		contradict BetS_A_B_P.
		exact nBetS_A_B_P.
	}
	apply Classical_Prop.NNPP in BetS_A_P_B_or_eq_B_P_or_BetS_A_B_P.
	exact BetS_A_P_B_or_eq_B_P_or_BetS_A_B_P.
Qed.

End Euclid.
