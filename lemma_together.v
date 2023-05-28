Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_lessthancongruence_smaller.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_together :
	forall A B C D F G P Q a b c,
	TogetherGreater A a B b C c ->
	Cong D F A a ->
	Cong F G B b ->
	BetS D F G ->
	Cong P Q C c ->
	Lt P Q D G /\ neq A a /\ neq B b /\ neq C c.
Proof.
	intros A B C D F G P Q a b c.
	intros TogetherGreater_A_a_B_b_C_c.
	intros Cong_DF_Aa.
	intros Cong_FG_Bb.
	intros BetS_D_F_G.
	intros Cong_PQ_Cc.

	pose proof (cn_congruencereflexive A a) as Cong_Aa_Aa.

	destruct TogetherGreater_A_a_B_b_C_c as (R & BetS_A_a_R & Cong_aR_Bb & Lt_Cc_AR).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_a_R) as (neq_a_R & neq_A_a & _).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_aR_Bb) as Cong_Bb_aR.
	pose proof (axiom_nocollapse _ _ _ _ neq_a_R Cong_aR_Bb) as neq_B_b.

	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_FG_Bb Cong_Bb_aR) as Cong_FG_aR.
	pose proof (cn_sumofparts _ _ _ _ _ _ Cong_DF_Aa Cong_FG_aR BetS_D_F_G BetS_A_a_R) as Cong_DG_AR.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_DG_AR) as Cong_AR_DG.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_PQ_Cc) as Cong_Cc_PQ.

	pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_Cc_AR Cong_Cc_PQ) as Lt_PQ_AR.
	pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_PQ_AR Cong_AR_DG) as Lt_PQ_DG.

	destruct Lt_Cc_AR as (S & BetS_A_S_R & Cong_AS_Cc).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_S_R) as (_ & neq_A_S & _).
	pose proof (axiom_nocollapse _ _ _ _ neq_A_S Cong_AS_Cc) as neq_C_c.

	split.
	exact Lt_PQ_DG.
	split.
	exact neq_A_a.
	split.
	exact neq_B_b.
	exact neq_C_c.
Qed.

End Euclid.
