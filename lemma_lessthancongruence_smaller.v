Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_s_lt.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_lessthancongruence_smaller :
	forall A B C D E F,
	Lt A B C D ->
	Cong A B E F ->
	Lt E F C D.
Proof.
	intros A B C D E F.
	intros Lt_A_B_C_D.
	intros Cong_A_B_E_F.

	destruct Lt_A_B_C_D as (G & BetS_C_G_D & Cong_C_G_A_B).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_C_G_A_B Cong_A_B_E_F) as Cong_C_G_E_F.
	pose proof (lemma_s_lt _ _ _ _ _ BetS_C_G_D Cong_C_G_E_F) as Lt_E_F_C_D.
	exact Lt_E_F_C_D.
Qed.

End Euclid.
