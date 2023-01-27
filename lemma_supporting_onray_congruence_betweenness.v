Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_supporting_lt.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_layoffunique.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_supporting_onray_congruence_betweenness :
	forall A B C a b c,
	Cong A B a b ->
	Cong A C a c ->
	OnRay a b c ->
	BetS A B C ->
	BetS a b c.
Proof.
	intros A B C a b c.
	intros Cong_AB_ab.
	intros Cong_AC_ac.
	intros OnRay_ab_c.
	intros BetS_A_B_C.

	pose proof (cn_congruencereflexive A B) as Cong_AB_AB.
	pose proof (lemma_supporting_lt _ _ _ _ _ BetS_A_B_C Cong_AB_AB) as Lt_AB_AC.
	pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_AB_AC Cong_AC_ac) as Lt_AB_ac.
	destruct Lt_AB_ac as (g & BetS_a_g_c & Cong_ag_AB).

	pose proof (lemma_betweennotequal _ _ _ BetS_a_g_c) as (_ & neq_a_g & _).
	assert (BetS a c g \/ eq c g \/ BetS a g c) as BetS_a_c_g_or_eq_c_g_or_BetS_a_g_c.
	one_of_disjunct BetS_a_g_c.
	pose proof (lemma_onray_assert _ _ _ BetS_a_c_g_or_eq_c_g_or_BetS_a_g_c neq_a_g) as OnRay_ag_c.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_ag_c) as OnRay_ac_g.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_ag_AB Cong_AB_ab) as Cong_ag_ab.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_ab_c) as OnRay_ac_b.
	pose proof (lemma_layoffunique _ _ _ _ OnRay_ac_g OnRay_ac_b Cong_ag_ab) as eq_g_b.
	assert (BetS_a_b_c := BetS_a_g_c).
	replace g with b in BetS_a_b_c.

	exact BetS_a_b_c.
Qed.

End Euclid.
