Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_equalanglesreflexive : 
	forall A B C,
	nCol A B C ->
	CongA A B C A B C.
Proof.
	intros A B C.
	intros nCol_A_B_C.

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_B_C) as CongA_A_B_C_C_B_A.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_A_B_C_C_B_A) as nCol_C_B_A.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_C_B_A) as CongA_C_B_A_A_B_C.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_B_C_C_B_A CongA_C_B_A_A_B_C) as CongA_A_B_C_A_B_C.
	exact CongA_A_B_C_A_B_C.
Qed.

End Euclid.
