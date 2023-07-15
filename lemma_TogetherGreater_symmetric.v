Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.by_def_TogetherGreater.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_TogetherGreater_symmetric :
	forall A B C a b c,
	TogetherGreater A a B b C c ->
	TogetherGreater B b A a C c.
Proof.
	intros A B C a b c.
	intros TogetherGreater_Aa_Bb_Cc.

	destruct TogetherGreater_Aa_Bb_Cc as (H & BetS_A_a_H & Cong_aH_Bb & Lt_Cc_AH).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_a_H) as (neq_a_H & neq_A_a  & _).
	pose proof (axiom_nocollapse _ _ _ _ neq_a_H Cong_aH_Bb) as neq_B_b.

	pose proof (lemma_extension _ _ _ _ neq_B_b neq_A_a) as (F & BetS_B_b_F & Cong_bF_Aa).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_b_F) as BetS_F_b_B.

	pose proof (lemma_doublereverse _ _ _ _ Cong_bF_Aa) as (Cong_aA_Fb & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_aA_Fb) as (_ & Cong_Aa_Fb & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_aH_Bb) as (_ & _ & Cong_aH_bB).


	pose proof (cn_sumofparts A _ H F _ B Cong_Aa_Fb Cong_aH_bB BetS_A_a_H BetS_F_b_B) as Cong_AH_FB.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AH_FB) as (_ & _ & Cong_AH_BF).

	pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_Cc_AH Cong_AH_BF) as Lt_Cc_BF.

	pose proof (by_def_TogetherGreater _ _ _ _ _ _ _ BetS_B_b_F Cong_bF_Aa Lt_Cc_BF) as TogetherGreater_Bb_Aa_Cc.

	exact TogetherGreater_Bb_Aa_Cc.
Qed.

End Euclid.
