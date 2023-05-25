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
	intros Cong_D_F_A_a.
	intros Cong_F_G_B_b.
	intros BetS_D_F_G.
	intros Cong_P_Q_C_c.

	destruct TogetherGreater_A_a_B_b_C_c as (R & BetS_A_a_R & Cong_a_R_B_b & Lt_C_c_A_R).
	pose proof (cn_congruencereflexive A a) as Cong_A_a_A_a.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_a_R_B_b) as Cong_B_b_a_R.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_F_G_B_b Cong_B_b_a_R) as Cong_F_G_a_R.
	pose proof (cn_sumofparts _ _ _ _ _ _ Cong_D_F_A_a Cong_F_G_a_R BetS_D_F_G BetS_A_a_R) as Cong_D_G_A_R.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_D_G_A_R) as Cong_A_R_D_G.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_P_Q_C_c) as Cong_C_c_P_Q.
	pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_C_c_A_R Cong_C_c_P_Q) as Lt_P_Q_A_R.
	pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_P_Q_A_R Cong_A_R_D_G) as Lt_P_Q_D_G.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_a_R) as (_ & neq_A_a & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_a_R) as (neq_a_R & _ & _).
	pose proof (axiom_nocollapse _ _ _ _ neq_a_R Cong_a_R_B_b) as neq_B_b.
	destruct Lt_C_c_A_R as (S & BetS_A_S_R & Cong_A_S_C_c).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_S_R) as (_ & neq_A_S & _).
	pose proof (axiom_nocollapse _ _ _ _ neq_A_S Cong_A_S_C_c) as neq_C_c.

	split.
	exact Lt_P_Q_D_G.
	split.
	exact neq_A_a.
	split.
	exact neq_B_b.
	exact neq_C_c.
Qed.

End Euclid.
