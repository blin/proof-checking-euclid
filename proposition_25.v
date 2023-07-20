Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_angletrichotomy_n_CongA_ABC_DEF_n_LtA_DEF_ABC_LtA_ABC_DEF.
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
	intros Triangle_ABC.
	intros Triangle_DEF.
	intros Cong_AB_DE.
	intros Cong_AC_DF.
	intros Lt_EF_BC.

	pose proof (lemma_s_ncol_triangle _ _ _ Triangle_ABC) as nCol_A_B_C.
	pose proof (lemma_s_ncol_triangle _ _ _ Triangle_DEF) as nCol_D_E_F.

	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (by_prop_nCol_order _ _ _ nCol_D_E_F) as (nCol_E_D_F & nCol_E_F_D & nCol_F_D_E & nCol_D_F_E & nCol_F_E_D).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AB_DE) as Cong_DE_AB.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AC_DF) as Cong_DF_AC.

	assert (~ LtA B A C E D F) as n_LtA_BAC_EDF.
	{
		intro LtA_BAC_EDF.

		pose proof (proposition_24 _ _ _ _ _ _ Triangle_DEF Triangle_ABC Cong_DE_AB Cong_DF_AC LtA_BAC_EDF) as Lt_BC_EF.
		pose proof (lemma_trichotomy_asymmetric _ _ _ _ Lt_BC_EF) as n_Lt_EF_BC.

		contradict Lt_EF_BC.
		exact n_Lt_EF_BC.
	}


	assert (~ CongA E D F B A C) as n_CongA_EDF_BAC.
	{
		intro CongA_EDF_BAC.

		pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_EDF_BAC) as CongA_BAC_EDF.
		pose proof (proposition_04 _ _ _ _ _ _ Cong_AB_DE Cong_AC_DF CongA_BAC_EDF) as (Cong_BC_EF & _ & _).
		pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BC_EF) as Cong_EF_BC.
		pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_EF_BC Cong_EF_BC) as Lt_BC_BC.
		pose proof (lemma_trichotomy_asymmetric _ _ _ _ Lt_BC_BC) as n_Lt_BC_BC.

		contradict Lt_BC_BC.
		exact n_Lt_BC_BC.
	}

	pose proof (lemma_angletrichotomy_n_CongA_ABC_DEF_n_LtA_DEF_ABC_LtA_ABC_DEF _ _ _ _ _ _ nCol_E_D_F nCol_B_A_C n_CongA_EDF_BAC n_LtA_BAC_EDF) as LtA_EDF_BAC.
	exact LtA_EDF_BAC.
Qed.

End Euclid.
