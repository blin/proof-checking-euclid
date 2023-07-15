Require Import ProofCheckingEuclid.by_def_TT.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_TogetherGreater_flip.
Require Import ProofCheckingEuclid.lemma_TogetherGreater_symmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_TTflip :
	forall A B C D E F G H,
	TT A B C D E F G H ->
	TT B A D C E F G H.
Proof.
	intros A B C D E F G H.
	intros TT_A_B_C_D_E_F_G_H.

	destruct TT_A_B_C_D_E_F_G_H as (J & BetS_E_F_J & Cong_FJ_GH & TogetherGreater_AB_CD_EJ).
	pose proof (lemma_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_AB_CD_EJ) as (TogetherGreater_BA_CD_EJ & _).
	pose proof (lemma_TogetherGreater_symmetric _ _ _ _ _ _ TogetherGreater_BA_CD_EJ) as TogetherGreater_CD_BA_EJ.
	pose proof (lemma_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_CD_BA_EJ) as (TogetherGreater_DC_BA_EJ & _).
	pose proof (lemma_TogetherGreater_symmetric _ _ _ _ _ _ TogetherGreater_DC_BA_EJ) as TogetherGreater_BA_DC_EJ.

	pose proof (by_def_TT _ _ _ _ _ _ _ _ _ BetS_E_F_J Cong_FJ_GH TogetherGreater_BA_DC_EJ) as TT_B_A_D_C_E_F_G_H.

	exact TT_B_A_D_C_E_F_G_H.
Qed.

End Euclid.
