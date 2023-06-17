Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angletrichotomy_n_CongA_ABC_DEF_n_LtA_DEF_ABC_LtA_ABC_DEF.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_lessthancongruence_smaller.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_trichotomy_asymmetric.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_24.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_25 :
	forall A B C D E F,
	Triangle A B C ->
	Triangle D E F ->
	Cong A B D E ->
	Cong A C D F ->
	Lt E F B C ->
	LtA E D F B A C.
Proof.
	intros A B C D E F.
	intros Triangle_A_B_C.
	intros Triangle_D_E_F.
	intros Cong_A_B_D_E.
	intros Cong_A_C_D_F.
	intros Lt_E_F_B_C.

	pose proof (lemma_s_ncol_triangle _ _ _ Triangle_A_B_C) as nCol_A_B_C.
	pose proof (lemma_s_ncol_triangle _ _ _ Triangle_D_E_F) as nCol_D_E_F.

	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (lemma_NCorder _ _ _ nCol_D_E_F) as (nCol_E_D_F & nCol_E_F_D & nCol_F_D_E & nCol_D_F_E & nCol_F_E_D).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_A_B_D_E) as Cong_D_E_A_B.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_A_C_D_F) as Cong_D_F_A_C.

	assert (~ LtA B A C E D F) as n_LtA_B_A_C_E_D_F.
	{
		intro LtA_B_A_C_E_D_F.

		pose proof (proposition_24 _ _ _ _ _ _ Triangle_D_E_F Triangle_A_B_C Cong_D_E_A_B Cong_D_F_A_C LtA_B_A_C_E_D_F) as Lt_B_C_E_F.
		pose proof (lemma_trichotomy_asymmetric _ _ _ _ Lt_B_C_E_F) as n_Lt_E_F_B_C.

		contradict Lt_E_F_B_C.
		exact n_Lt_E_F_B_C.
	}


	assert (~ CongA E D F B A C) as n_CongA_E_D_F_B_A_C.
	{
		intro CongA_E_D_F_B_A_C.

		pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_E_D_F_B_A_C) as CongA_B_A_C_E_D_F.
		pose proof (proposition_04 _ _ _ _ _ _ Cong_A_B_D_E Cong_A_C_D_F CongA_B_A_C_E_D_F) as (Cong_B_C_E_F & _ & _).
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_B_C_E_F) as Cong_E_F_B_C.
		pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_E_F_B_C Cong_E_F_B_C) as Lt_B_C_B_C.
		pose proof (lemma_trichotomy_asymmetric _ _ _ _ Lt_B_C_B_C) as n_Lt_B_C_B_C.

		contradict Lt_B_C_B_C.
		exact n_Lt_B_C_B_C.
	}

	pose proof (lemma_angletrichotomy_n_CongA_ABC_DEF_n_LtA_DEF_ABC_LtA_ABC_DEF _ _ _ _ _ _ nCol_E_D_F nCol_B_A_C n_CongA_E_D_F_B_A_C n_LtA_B_A_C_E_D_F) as LtA_E_D_F_B_A_C.
	exact LtA_E_D_F_B_A_C.
Qed.

End Euclid.
