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
	intros CongA_ABC_DEF.

	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_ABC_DEF) as nCol_D_E_F.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_ABC_DEF) as CongA_DEF_ABC.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_DEF_ABC) as nCol_A_B_C.

	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (_ & _ & _ & _ & nCol_C_B_A).

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_C_B_A) as CongA_CBA_ABC.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_CBA_ABC CongA_ABC_DEF) as CongA_CBA_DEF.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_D_E_F) as CongA_DEF_FED.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_CBA_DEF CongA_DEF_FED) as CongA_CBA_FED.

	exact CongA_CBA_FED.
Qed.

End Euclid.
