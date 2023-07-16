Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_def_LtA.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_angletrichotomy.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_trichotomy_equal.
Require Import ProofCheckingEuclid.proposition_04.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_26A :
	forall A B C D E F,
	Triangle A B C ->
	Triangle D E F ->
	CongA A B C D E F ->
	CongA B C A E F D ->
	Cong B C E F ->
	Cong A B D E /\ Cong A C D F /\ CongA B A C E D F.
Proof.
	intros A B C D E F.
	intros Triangle_ABC.
	intros Triangle_DEF.
	intros CongA_ABC_DEF.
	intros CongA_BCA_EFD.
	intros Cong_BC_EF.

	pose proof (cn_congruencereflexive B C) as Cong_BC_BC.
	pose proof (cn_congruencereflexive E F) as Cong_EF_EF.
	pose proof (cn_congruencereverse A B) as Cong_AB_BA.
	pose proof (cn_congruencereverse D E) as Cong_DE_ED.

	pose proof (lemma_s_ncol_triangle _ _ _ Triangle_ABC) as nCol_A_B_C.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).

	pose proof (lemma_s_ncol_triangle _ _ _ Triangle_DEF) as nCol_D_E_F.
	pose proof (lemma_NCdistinct _ _ _ nCol_D_E_F) as (neq_D_E & neq_E_F & neq_D_F & neq_E_D & neq_F_E & neq_F_D).

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_F_D) as OnRay_FD_D.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_F_E) as OnRay_FE_E.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_E_F) as OnRay_EF_F.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_A) as OnRay_CA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_B) as OnRay_CB_B.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_C) as OnRay_BC_C.

	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_ABC_DEF) as CongA_DEF_ABC.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_BCA_EFD) as CongA_EFD_BCA.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BC_EF) as Cong_EF_BC.

	assert (~ Lt D E A B) as n_Lt_DE_AB.
	{
		intro Lt_DE_AB.

		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_DE_AB Cong_AB_BA) as Lt_DE_BA.

		destruct Lt_DE_BA as (G & BetS_B_G_A & Cong_BG_DE).

		pose proof (lemma_betweennotequal _ _ _ BetS_B_G_A) as (_ & neq_B_G & _).
		pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_G) as OnRay_BG_G.
		pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_B_G_A neq_B_A) as OnRay_BA_G.

		pose proof (lemma_congruenceflip _ _ _ _ Cong_BG_DE) as (_ & _ & Cong_BG_ED).
		pose proof (cn_congruencereflexive B G) as Cong_BG_BG.
		pose proof (cn_congruencereflexive G C) as Cong_GC_GC.

		pose proof (by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_BA_G OnRay_BC_C OnRay_BG_G OnRay_BC_C Cong_BG_BG Cong_BC_BC Cong_GC_GC nCol_A_B_C) as CongA_ABC_GBC.
		pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_ABC_GBC) as CongA_GBC_ABC.
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_GBC_ABC CongA_ABC_DEF) as CongA_GBC_DEF.

		pose proof (proposition_04 _ _ _ _ _ _ Cong_BG_ED Cong_BC_EF CongA_GBC_DEF) as (_ & _ & CongA_BCG_EFD).
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_BCG_EFD CongA_EFD_BCA) as CongA_BCG_BCA.
		pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_BCG_BCA) as CongA_BCA_BCG.
		pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_B_G_A OnRay_CB_B OnRay_CA_A CongA_BCA_BCG) as LtA_BCA_BCA.
		pose proof (lemma_angletrichotomy _ _ _ _ _ _ LtA_BCA_BCA) as n_LtA_BCA_BCA.

		contradict LtA_BCA_BCA.
		exact n_LtA_BCA_BCA.
	}

	assert (~ Lt A B D E) as n_Lt_AB_DE.
	{
		intro Lt_AB_DE.

		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_AB_DE Cong_DE_ED) as Lt_AB_ED.

		destruct Lt_AB_ED as (G & BetS_E_G_D & Cong_EG_AB).

		pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_E_G_D neq_E_D) as OnRay_ED_G.
		pose proof (lemma_onray_strict _ _ _ OnRay_ED_G) as neq_E_G.
		pose proof (by_def_OnRay_from_neq_A_B _ _ neq_E_G) as OnRay_EG_G.

		pose proof (lemma_congruenceflip _ _ _ _ Cong_EG_AB) as (_ & _ & Cong_EG_BA).
		pose proof (cn_congruencereflexive E G) as Cong_EG_EG.
		pose proof (cn_congruencereflexive G F) as Cong_GF_GF.

		pose proof (by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_ED_G OnRay_EF_F OnRay_EG_G OnRay_EF_F Cong_EG_EG Cong_EF_EF Cong_GF_GF nCol_D_E_F) as CongA_DEF_GEF.
		pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_DEF_GEF) as CongA_GEF_DEF.
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_GEF_DEF CongA_DEF_ABC) as CongA_GEF_ABC.

		pose proof (proposition_04 _ _ _ _ _ _ Cong_EG_BA Cong_EF_BC CongA_GEF_ABC) as (_ & _ & CongA_EFG_BCA).
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_EFG_BCA CongA_BCA_EFD) as CongA_EFG_EFD.
		pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_EFG_EFD) as CongA_EFD_EFG.
		pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_E_G_D OnRay_FE_E OnRay_FD_D CongA_EFD_EFG) as LtA_EFD_EFD.
		pose proof (lemma_angletrichotomy _ _ _ _ _ _ LtA_EFD_EFD) as n_LtA_EFD_EFD.

		contradict LtA_EFD_EFD.
		exact n_LtA_EFD_EFD.
	}

	pose proof (lemma_trichotomy_equal _ _ _ _ n_Lt_AB_DE n_Lt_DE_AB neq_A_B neq_D_E) as Cong_AB_DE.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AB_DE) as (Cong_BA_ED & _ & _).
	pose proof (proposition_04 _ _ _ _ _ _ Cong_BA_ED Cong_BC_EF CongA_ABC_DEF) as (Cong_AC_DF & CongA_BAC_EDF & _).

	split.
	exact Cong_AB_DE.
	split.
	exact Cong_AC_DF.
	exact CongA_BAC_EDF.
Qed.

End Euclid.
