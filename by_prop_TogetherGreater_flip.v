Require Import ProofCheckingEuclid.by_def_TogetherGreater.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_TogetherGreater_flip :
	forall A B C a b c,
	TogetherGreater A a B b C c ->
	TogetherGreater a A B b C c /\ TogetherGreater A a B b c C.
Proof.
	intros A B C a b c.
	intros TogetherGreater_Aa_Bb_Cc.

	pose proof (cn_congruencereverse A a) as Cong_Aa_aA.
	pose proof (cn_congruencereverse C c) as Cong_Cc_cC.

	destruct TogetherGreater_Aa_Bb_Cc as (H & BetS_A_a_H & Cong_aH_Bb & Lt_Cc_AH).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_a_H) as (neq_a_H  & neq_A_a & _).
	pose proof (by_prop_neq_symmetric _ _ neq_A_a) as neq_a_A.
	pose proof (axiom_nocollapse _ _ _ _ neq_a_H Cong_aH_Bb) as neq_B_b.
	pose proof (lemma_extension _ _ _ _ neq_a_A neq_B_b) as (h & BetS_a_A_h & Cong_Ah_Bb).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_Ah_Bb) as Cong_Bb_Ah.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_aH_Bb Cong_Bb_Ah) as Cong_aH_Ah.
	pose proof (cn_sumofparts A a H a A h Cong_Aa_aA Cong_aH_Ah BetS_A_a_H BetS_a_A_h) as Cong_AH_ah.

	pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_Cc_AH Cong_AH_ah) as Lt_Cc_ah.
	pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_Cc_AH Cong_Cc_cC) as Lt_cC_AH.

	pose proof (by_def_TogetherGreater _ _ _ _ _ _ _ BetS_a_A_h Cong_Ah_Bb Lt_Cc_ah) as TogetherGreater_aA_Bb_Cc.
	pose proof (by_def_TogetherGreater _ _ _ _ _ _ _ BetS_A_a_H Cong_aH_Bb Lt_cC_AH) as TogetherGreater_Aa_Bb_cC.

	split.
	exact TogetherGreater_aA_Bb_Cc.
	exact TogetherGreater_Aa_Bb_cC.
Qed.

End Euclid.
