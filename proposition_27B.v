Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_collinearparallel.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_parallelflip.
Require Import ProofCheckingEuclid.lemma_parallelsymmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.proposition_27.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_27B :
	forall A D E F,
	CongA A E F E F D ->
	OS A E F D ->
	Par A E F D.
Proof.
	intros A D E F.
	intros CongA_AEF_EFD.
	intros OS_A_EF_D.

	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_AEF_EFD) as (neq_A_E & _ & _ & _ & _ & _).
	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_AEF_EFD) as (_ & _ & _ & _ & neq_F_D & _).

	pose proof (lemma_inequalitysymmetric _ _ neq_A_E) as neq_E_A.
	pose proof (lemma_inequalitysymmetric _ _ neq_F_D) as neq_D_F.

	pose proof (postulate_Euclid2 _ _ neq_A_E) as (B & BetS_A_E_B).
	pose proof (postulate_Euclid2 _ _ neq_D_F) as (C & BetS_D_F_C).

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_E_B) as Col_A_E_B.
	pose proof (lemma_collinearorder _ _ _ Col_A_E_B) as (_ & _ & Col_B_A_E & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_F_C) as BetS_C_F_D.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_D_F_C) as Col_D_F_C.
	pose proof (lemma_collinearorder _ _ _ Col_D_F_C) as (_ & _ & Col_C_D_F & _ & _).

	pose proof (proposition_27 _ _ _ _ _ _ BetS_A_E_B BetS_C_F_D CongA_AEF_EFD OS_A_EF_D) as Par_AB_CD.

	pose proof (lemma_collinearparallel _ _ _ _ _ Par_AB_CD Col_C_D_F neq_F_D) as Par_AB_FD.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_AB_FD) as Par_FD_AB.
	pose proof (lemma_parallelflip _ _ _ _ Par_FD_AB) as (_ & Par_FD_BA & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_FD_BA Col_B_A_E neq_E_A) as Par_FD_EA.
	pose proof (lemma_parallelflip _ _ _ _ Par_FD_EA) as (_ & Par_FD_AE & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_FD_AE) as Par_AE_FD.

	exact Par_AE_FD.
Qed.

End Euclid.
