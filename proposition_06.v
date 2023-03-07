Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_trichotomy1.
Require Import ProofCheckingEuclid.proposition_06a.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_06 : 
	forall A B C,
	Triangle A B C ->
	CongA A B C A C B ->
	Cong A B A C.
Proof.
	intros A B C.
	intros Triangle_A_B_C.
	intros CongA_A_B_C_A_C_B.

	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_A_B_C_A_C_B) as (neq_A_B & neq_B_C & neq_A_C & _ & neq_C_B & _).
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_B_C_A_C_B) as Conga_A_C_B_A_B_C.

	assert (nCol A B C) as nCol_A_B_C by (unfold Triangle in Triangle_A_B_C; exact Triangle_A_B_C).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	assert (Triangle A C B) as Triangle_A_C_B by (unfold Triangle; exact nCol_A_C_B ).

	pose proof (proposition_06a _ _ _ Triangle_A_B_C CongA_A_B_C_A_C_B) as n_Lt_A_C_A_B.
	pose proof (proposition_06a _ _ _ Triangle_A_C_B Conga_A_C_B_A_B_C) as n_Lt_A_B_A_C.
	pose proof (lemma_trichotomy1 A B A C n_Lt_A_B_A_C n_Lt_A_C_A_B neq_A_B neq_A_C) as Cong_A_B_A_C.

	exact Cong_A_B_A_C.
Qed.

End Euclid.
