Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_equalanglesflip :
	forall A B C D E F,
	CongA A B C D E F ->
	CongA C B A F E D.
Proof.
	intros A B C D E F.
	intros CongA_A_B_C_D_E_F.

	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_A_B_C_D_E_F) as nCol_D_E_F.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_B_C_D_E_F) as CongA_D_E_F_A_B_C.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_D_E_F_A_B_C) as nCol_A_B_C.

	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_C_B_A) as CongA_C_B_A_A_B_C.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_C_B_A_A_B_C CongA_A_B_C_D_E_F) as CongA_C_B_A_D_E_F.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_D_E_F) as CongA_D_E_F_F_E_D.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_C_B_A_D_E_F CongA_D_E_F_F_E_D) as CongA_C_B_A_F_E_D.

	exact CongA_C_B_A_F_E_D.
Qed.

End Euclid.
