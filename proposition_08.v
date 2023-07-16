Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Coq.Logic.Classical_Prop.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_08 :
	forall A B C D E F,
	Triangle A B C ->
	Triangle D E F ->
	Cong A B D E ->
	Cong A C D F ->
	Cong B C E F ->
	CongA B A C E D F /\ CongA C B A F E D /\ CongA A C B D F E.
Proof.
	intros A B C D E F.
	intros Triangle_ABC.
	intros Triangle_DEF.
	intros Cong_AB_DE.
	intros Cong_AC_DF.
	intros Cong_BC_EF.

	assert (nCol A B C) as nCol_A_B_C by (unfold Triangle in Triangle_ABC; exact Triangle_ABC).
	assert (nCol D E F) as nCol_D_E_F by (unfold Triangle in Triangle_DEF; exact Triangle_DEF).

	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).
	pose proof (lemma_NCdistinct _ _ _ nCol_D_E_F) as (neq_D_E & neq_E_F & neq_D_F & neq_E_D & neq_F_E & neq_F_D).

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_D_E) as OnRay_DE_E.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_D_F) as OnRay_DF_F.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_A_B) as OnRay_AB_B.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_A_C) as OnRay_AC_C.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_E_F) as OnRay_EF_F.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_E_D) as OnRay_ED_D.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_C) as OnRay_BC_C.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_A) as OnRay_BA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_F_D) as OnRay_FD_D.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_F_E) as OnRay_FE_E.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_A) as OnRay_CA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_B) as OnRay_CB_B.

	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & _ & _ & nCol_A_C_B & nCol_C_B_A).

	pose proof (lemma_congruenceflip _ _ _ _ Cong_AB_DE) as (Cong_BA_ED & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AC_DF) as (Cong_CA_FD & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_BC_EF) as (Cong_CB_FE & _ & _).

	pose proof (
		by_def_CongA
		_ _ _ _ _ _
		_ _ _ _
		OnRay_AB_B
		OnRay_AC_C
		OnRay_DE_E
		OnRay_DF_F
		Cong_AB_DE
		Cong_AC_DF
		Cong_BC_EF
		nCol_B_A_C
	) as CongA_BAC_EDF.

	pose proof (
		by_def_CongA
		_ _ _ _ _ _
		_ _ _ _
		OnRay_BC_C
		OnRay_BA_A
		OnRay_EF_F
		OnRay_ED_D
		Cong_BC_EF
		Cong_BA_ED
		Cong_CA_FD
		nCol_C_B_A
	) as CongA_CBA_FED.

	pose proof (
		by_def_CongA
		A C B D F E
		_ _ _ _
		OnRay_CA_A
		OnRay_CB_B
		OnRay_FD_D
		OnRay_FE_E
		Cong_CA_FD
		Cong_CB_FE
		Cong_AB_DE
		nCol_A_C_B
	) as CongA_ACB_DFE.

	split.
	exact CongA_BAC_EDF.
	split.
	exact CongA_CBA_FED.
	exact CongA_ACB_DFE.

Qed.

End Euclid.
