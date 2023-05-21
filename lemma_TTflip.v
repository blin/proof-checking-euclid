Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_TogetherGreater_flip.
Require Import ProofCheckingEuclid.lemma_TogetherGreater_symmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_lt.
Require Import ProofCheckingEuclid.lemma_s_lta.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_triangle.
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

	destruct TT_A_B_C_D_E_F_G_H as (J & BetS_E_F_J & Cong_F_J_G_H & TogetherGreater_A_B_C_D_E_J).
	epose proof (lemma_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_A_B_C_D_E_J) as (TogetherGreater_B_A_C_D_E_J & _).
	pose proof (lemma_TogetherGreater_symmetric _ _ _ _ _ _ TogetherGreater_B_A_C_D_E_J) as TogetherGreater_C_D_B_A_E_J.
	epose proof (lemma_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_C_D_B_A_E_J) as (TogetherGreater_D_C_B_A_E_J & _).
	pose proof (lemma_TogetherGreater_symmetric _ _ _ _ _ _ TogetherGreater_D_C_B_A_E_J) as TogetherGreater_B_A_D_C_E_J.

	epose proof (lemma_s_TT B A D C E F G H J BetS_E_F_J Cong_F_J_G_H TogetherGreater_B_A_D_C_E_J) as TT_B_A_D_C_E_F_G_H.

	exact TT_B_A_D_C_E_F_G_H.
Qed.

End Euclid.
