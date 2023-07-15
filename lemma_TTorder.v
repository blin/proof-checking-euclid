Require Import ProofCheckingEuclid.by_def_TT.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_TogetherGreater_symmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.


Lemma lemma_TTorder :
	forall A B C D E F G H,
	TT A B C D E F G H ->
	TT C D A B E F G H.
Proof.
	intros A B C D E F G H.
	intros TT_A_B_C_D_E_F_G_H.

	destruct TT_A_B_C_D_E_F_G_H as (J & BetS_E_F_J & Cong_FJ_GH & TogetherGreater_AB_CD_EJ).

	pose proof (lemma_TogetherGreater_symmetric _ _ _ _ _ _ TogetherGreater_AB_CD_EJ) as TogetherGreater_CD_AB_EJ.

	pose proof (by_def_TT _ _ _ _ _ _ _ _ _ BetS_E_F_J Cong_FJ_GH TogetherGreater_CD_AB_EJ) as TT_C_D_A_B_E_F_G_H.

	exact TT_C_D_A_B_E_F_G_H.
Qed.

End Euclid.
