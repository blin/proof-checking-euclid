Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_trichotomy_equal.
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
	intros Triangle_ABC.
	intros CongA_ABC_ACB.

	assert (nCol A B C) as nCol_A_B_C by (unfold Triangle in Triangle_ABC; exact Triangle_ABC).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (_ & _ & _ & nCol_A_C_B & _).
	assert (Triangle A C B) as Triangle_ACB by (unfold Triangle; exact nCol_A_C_B ).

	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_ABC_ACB) as (neq_A_B & _ & neq_A_C & _ & _ & _).
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_ABC_ACB) as CongA_ACB_ABC.

	pose proof (proposition_06a _ _ _ Triangle_ABC CongA_ABC_ACB) as n_Lt_AC_AB.
	pose proof (proposition_06a _ _ _ Triangle_ACB CongA_ACB_ABC) as n_Lt_AB_AC.

	pose proof (lemma_trichotomy_equal _ _ _ _ n_Lt_AB_AC n_Lt_AC_AB neq_A_B neq_A_C) as Cong_AB_AC.

	exact Cong_AB_AC.
Qed.

End Euclid.
