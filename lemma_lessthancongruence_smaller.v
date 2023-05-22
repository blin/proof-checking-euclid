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
	intros Lt_AB_CD.
	intros Cong_AB_EF.

	destruct Lt_AB_CD as (G & BetS_C_G_D & Cong_CG_AB).

	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_CG_AB Cong_AB_EF) as Cong_CG_EF.

	pose proof (lemma_s_lt _ _ _ _ _ BetS_C_G_D Cong_CG_EF) as Lt_EF_CD.

	exact Lt_EF_CD.
Qed.

End Euclid.
