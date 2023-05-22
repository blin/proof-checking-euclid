Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_TogetherGreater_flip.
Require Import ProofCheckingEuclid.lemma_TogetherGreater_symmetric.
Require Import ProofCheckingEuclid.lemma_s_TT.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_TTflip :
	forall A B C D E F G H,
	TT A B C D E F G H ->
	TT B A D C E F G H.
Proof.
	intros A B C D E F G H.
	intros TT_A_B_C_D_E_F_G_H.

	destruct TT_A_B_C_D_E_F_G_H as (J & BetS_E_F_J & Cong_FJ_GH & TogetherGreater_A_B_C_D_E_J).
	pose proof (lemma_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_A_B_C_D_E_J) as (TogetherGreater_B_A_C_D_E_J & _).
	pose proof (lemma_TogetherGreater_symmetric _ _ _ _ _ _ TogetherGreater_B_A_C_D_E_J) as TogetherGreater_C_D_B_A_E_J.
	pose proof (lemma_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_C_D_B_A_E_J) as (TogetherGreater_D_C_B_A_E_J & _).
	pose proof (lemma_TogetherGreater_symmetric _ _ _ _ _ _ TogetherGreater_D_C_B_A_E_J) as TogetherGreater_B_A_D_C_E_J.

	pose proof (lemma_s_TT _ _ _ _ _ _ _ _ _ BetS_E_F_J Cong_FJ_GH TogetherGreater_B_A_D_C_E_J) as TT_B_A_D_C_E_F_G_H.

	exact TT_B_A_D_C_E_F_G_H.
Qed.

End Euclid.
