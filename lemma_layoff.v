Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_s_onray.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_layoff : 
	forall A B C D,
	neq A B ->
	neq C D ->
	exists X, OnRay A B X /\ Cong A X C D.
Proof.
	intros A B C D.
	intros neq_A_B.
	intros neq_C_D.

	pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.

	pose proof (lemma_extension _ _ _ _ neq_B_A neq_C_D) as (E & BetS_B_A_E & Cong_AE_CD).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_E) as BetS_E_A_B.
	pose proof (lemma_betweennotequal _ _ _ BetS_E_A_B) as (_ & neq_E_A & _).

	pose proof (lemma_extension _ _ _ _ neq_E_A neq_C_D) as (P & BetS_E_A_P & Cong_AP_CD).

	pose proof (lemma_s_onray _ _ _ _ BetS_E_A_B BetS_E_A_P) as OnRay_AB_P.

	exists P.
	split.
	exact OnRay_AB_P.
	exact Cong_AP_CD.
Qed.

End Euclid.
