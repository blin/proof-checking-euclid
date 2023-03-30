Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennesspreserved.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_differenceofparts.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_interior5.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_s_cut.
Require Import ProofCheckingEuclid.lemma_s_intersecting_triangles_ncol_ADE.
Require Import ProofCheckingEuclid.lemma_s_intersecting_triangles_ncol_BDE.
Require Import ProofCheckingEuclid.lemma_s_lt.
Require Import ProofCheckingEuclid.lemma_twolines.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_intersecting_triangles_cong_AF_BF :
	forall A B D E F,
	Triangle A B D ->
	Triangle B A E ->
	BetS A F D ->
	BetS B F E ->
	Cong A D B E  ->
	Cong A E B D ->
	Cong A F B F.
Proof.
	intros A B D E F.
	intros Triangle_ABD.
	intros Triangle_BAE.
	intros BetS_A_F_D.
	intros BetS_B_F_E.
	intros Cong_AD_BE.
	intros Cong_AE_BD.

	pose proof (
		lemma_s_intersecting_triangles_ncol_ADE
		_ _ _ _ _
		Triangle_ABD Triangle_BAE BetS_A_F_D BetS_B_F_E
	) as nCol_A_D_E.
	pose proof (
		lemma_s_intersecting_triangles_ncol_BDE
		_ _ _ _ _
		Triangle_ABD Triangle_BAE BetS_A_F_D BetS_B_F_E
	) as nCol_B_D_E.

	assert (nCol_A_B_D := Triangle_ABD).
	unfold Triangle in nCol_A_B_D.
	pose proof (lemma_NCorder _ _ _ nCol_A_B_D) as (_ & _ & _ & nCol_A_D_B & _).
	pose proof (lemma_NCorder _ _ _ nCol_B_D_E) as (_ & nCol_D_E_B & _ & _ & _).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AE_BD) as Cong_BD_AE.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AD_BE) as Cong_BE_AD.

	pose proof (cn_congruencereverse B A) as Cong_BA_AB.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_F_E) as BetS_E_F_B.

	pose proof (cn_congruencereflexive B F) as Cong_BF_BF.
	pose proof (lemma_s_lt _ _ _ _ _ BetS_B_F_E Cong_BF_BF) as Lt_BF_BE.
	pose proof (
		lemma_lessthancongruence _ _ _ _ _ _ Lt_BF_BE Cong_BE_AD
	) as (G & BetS_A_G_D & Cong_AG_BF).

	pose proof (
		lemma_differenceofparts _ _ _ _ _ _ Cong_AG_BF Cong_AD_BE BetS_A_G_D BetS_B_F_E
	) as Cong_GD_FE.
	pose proof (lemma_doublereverse _ _ _ _ Cong_GD_FE) as (Cong_EF_DG & _).
	pose proof (lemma_doublereverse _ _ _ _ Cong_AG_BF) as (Cong_FB_GA & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AE_BD) as (Cong_EA_DB & _ & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_G_D) as BetS_D_G_A.
	pose proof (
		lemma_interior5
		E F B A
		D G A B

		BetS_E_F_B
		BetS_D_G_A

		Cong_EF_DG
		Cong_FB_GA

		Cong_EA_DB
		Cong_BA_AB
	) as Cong_FA_GB.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_FA_GB) as (Cong_AF_BG & _ & _).
	pose proof (cn_congruencereverse E D) as Cong_ED_DE.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AG_BF) as Cong_BF_AG.
	pose proof (lemma_doublereverse _ _ _ _ Cong_EF_DG) as (_ & Cong_FE_GD).
	pose proof (
		lemma_interior5
		B F E D
		A G D E

		BetS_B_F_E
		BetS_A_G_D

		Cong_BF_AG
		Cong_FE_GD

		Cong_BD_AE
		Cong_ED_DE
	) as Cong_FD_GE.
	pose proof (
		lemma_betweennesspreserved
		_ _ D B G E
		Cong_AF_BG
		Cong_AD_BE
		Cong_FD_GE
		BetS_A_F_D
	) as BetS_B_G_E.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_G_E) as BetS_E_G_B.

	pose proof (lemma_s_cut _ _ _ _ _ BetS_A_G_D BetS_E_G_B nCol_A_D_E nCol_A_D_B) as Cut_AD_EB_G.
	pose proof (lemma_s_cut _ _ _ _ _ BetS_A_F_D BetS_E_F_B nCol_A_D_E nCol_A_D_B) as Cut_AD_EB_F.

	pose proof (lemma_twolines _ _ _ _ _ _ Cut_AD_EB_G Cut_AD_EB_F nCol_D_E_B) as eq_G_F.
	assert (Cong A F B F) as Cong_AF_BF by (setoid_rewrite <- eq_G_F at 2; exact Cong_AF_BG).
	exact Cong_AF_BF.
Qed.

End Euclid.
