Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Cut.
Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennesspreserved.
Require Import ProofCheckingEuclid.lemma_differenceofparts.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_interior5.
Require Import ProofCheckingEuclid.lemma_s_5_line.
Require Import ProofCheckingEuclid.lemma_s_Col_ABC_nCol_ABD_nCol_ACD.
Require Import ProofCheckingEuclid.lemma_s_Pasch_inner.
Require Import ProofCheckingEuclid.lemma_twolines.
Require Import ProofCheckingEuclid.proposition_01.


Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_10 :
	forall A B,
	neq A B ->
	exists X, BetS A X B /\ Cong X A X B.
Proof.
	intros A B.
	intros neq_A_B.

	pose proof (cn_congruencereverse A B) as Cong_AB_BA.

	pose proof (proposition_01 _ _ neq_A_B) as (C & equilateral_ABC & Triangle_ABC).

	(*
		Doesn't actually have to be equilateral,
		isosceles is sufficient.
	*)
	destruct equilateral_ABC as (_ & Cong_BC_CA).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BC_CA) as Cong_CA_BC.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BC_CA) as (_ & _ & Cong_BC_AC).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_CA_BC) as (_ & _ & Cong_CA_CB).

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_ABC) as nCol_A_B_C.

	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_C) as n_Col_A_B_C.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (_ & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).

	pose proof (postulate_Euclid2 _ _ neq_C_B) as (D & BetS_C_B_D).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_B_D) as BetS_D_B_C.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_B_D) as (neq_B_D & _ & neq_C_D).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_D_B_C) as (_& neq_D_B & neq_D_C).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_B_D) as Col_C_B_D.
	pose proof (by_prop_Col_order _ _ _ Col_C_B_D) as (Col_B_C_D & Col_B_D_C & Col_D_C_B & Col_C_D_B & Col_D_B_C).

	pose proof (lemma_extension _ _ _ _ neq_C_A neq_B_D) as (E & BetS_C_A_E & Cong_AE_BD).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_A_E) as BetS_E_A_C.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_A_E) as (neq_A_E & _ & neq_C_E).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_A_C) as (_& neq_E_A & neq_E_C).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_A_E) as Col_C_A_E.
	pose proof (by_prop_Col_order _ _ _ Col_C_A_E) as (Col_A_C_E & Col_A_E_C & Col_E_C_A & Col_C_E_A & Col_E_A_C).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AE_BD) as Cong_BD_AE.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BD_AE) as (Cong_DB_EA & _ & _).

	pose proof (cn_sumofparts _ _ _ _ _ _ Cong_CA_CB Cong_AE_BD BetS_C_A_E BetS_C_B_D) as Cong_CE_CD.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_CE_CD) as Cong_CD_CE.

	pose proof (lemma_s_Col_ABC_nCol_ABD_nCol_ACD _ _ _ _ Col_C_B_D nCol_C_B_A neq_C_D) as nCol_C_D_A.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_C_D_A) as (_ & neq_D_A & _& _& neq_A_D &_).
	pose proof (by_prop_nCol_order _ _ _ nCol_C_D_A) as (nCol_D_C_A & nCol_D_A_C & nCol_A_C_D & nCol_C_A_D & nCol_A_D_C).

	pose proof (lemma_s_Col_ABC_nCol_ABD_nCol_ACD _ _ _ _ Col_C_A_E nCol_C_A_D neq_C_E) as nCol_C_E_D.

	pose proof (lemma_s_Col_ABC_nCol_ABD_nCol_ACD _ _ _ _ Col_C_A_E nCol_C_A_B neq_C_E) as nCol_C_E_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_C_E_B) as (nCol_E_C_B & nCol_E_B_C & nCol_B_C_E & nCol_C_B_E & nCol_B_E_C).

	pose proof (lemma_s_Col_ABC_nCol_ABD_nCol_ACD _ _ _ _ Col_B_C_D nCol_B_C_A neq_B_D) as nCol_B_D_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_B_D_A) as (nCol_D_B_A & nCol_D_A_B & nCol_A_B_D & nCol_B_A_D & nCol_A_D_B).

	assert (~ Col A D E) as n_Col_A_D_E.
	{
		intros Col_A_D_E.

		pose proof (by_prop_Col_order _ _ _ Col_A_D_E) as (Col_D_A_E & Col_D_E_A & Col_E_A_D & Col_A_E_D & Col_E_D_A).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_E_A_C Col_E_A_D neq_E_A) as Col_A_C_D.
		pose proof (by_prop_Col_order _ _ _ Col_A_C_D) as (Col_C_A_D & Col_C_D_A & Col_D_A_C & Col_A_D_C & Col_D_C_A).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_C_A Col_D_C_B neq_D_C) as Col_C_A_B.
		pose proof (by_prop_Col_order _ _ _ Col_C_A_B) as (Col_A_C_B & Col_A_B_C & Col_B_C_A & Col_C_B_A & Col_B_A_C).

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_A_D_E) as nCol_A_D_E.

	assert (~ Col D B E) as n_Col_D_B_E.
	{
		intros Col_D_B_E.

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_B_E Col_D_B_C neq_D_B) as Col_B_E_C.
		pose proof (by_prop_Col_order _ _ _ Col_B_E_C) as (Col_E_B_C & Col_E_C_B & Col_C_B_E & Col_B_C_E & Col_C_E_B).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_E_C_A Col_E_C_B neq_E_C) as Col_C_A_B.
		pose proof (by_prop_Col_order _ _ _ Col_C_A_B) as (Col_A_C_B & Col_A_B_C & Col_B_C_A & Col_C_B_A & Col_B_A_C).

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_D_B_E) as nCol_D_B_E.

	pose proof (lemma_s_5_line _ _ _ _ _ _ _ _ Cong_CA_CB Cong_AB_BA Cong_BC_AC BetS_C_A_E BetS_C_B_D Cong_AE_BD) as Cong_EB_DA.

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_EB_DA) as Cong_DA_EB.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_DA_EB) as (Cong_AD_BE & _ & _).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AD_BE) as Cong_BE_AD.

	pose proof (lemma_s_Pasch_inner _ _ _ _ _ BetS_C_B_D BetS_C_A_E nCol_C_E_D) as (F & BetS_D_F_A & BetS_B_F_E).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_F_A) as BetS_A_F_D.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_D_F_A) as (neq_F_A & neq_D_F &_).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_F_E) as BetS_E_F_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_F_E) as (neq_F_E & neq_B_F & neq_B_E).

	pose proof (cn_congruencereflexive B F) as Cong_BF_BF.
	pose proof (cn_congruencereflexive A F) as Cong_AF_AF.
	pose proof (cn_congruencereverse D E) as Cong_DE_ED.

	pose proof (by_def_Lt _ _ _ _ _ BetS_B_F_E Cong_BF_BF) as Lt_BF_BE.
	pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_BF_BE Cong_BE_AD) as Lt_BF_AD.
	destruct Lt_BF_AD as (G & BetS_A_G_D & Cong_AG_BF).

	pose proof (lemma_differenceofparts _ _ _ _ _ _ Cong_AG_BF Cong_AD_BE BetS_A_G_D BetS_B_F_E) as Cong_GD_FE.

	pose proof (lemma_interior5 _ _ _ _ _ _ _ _ BetS_A_G_D BetS_B_F_E Cong_AG_BF Cong_GD_FE Cong_AB_BA Cong_DB_EA) as Cong_GB_FA.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_GB_FA) as Cong_FA_GB.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_FA_GB) as (Cong_AF_BG & _ & _).

	pose proof (lemma_interior5 _ _ _ _ _ _ _ _ BetS_A_G_D BetS_B_F_E Cong_AG_BF Cong_GD_FE Cong_AE_BD Cong_DE_ED) as Cong_GE_FD.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_GE_FD) as Cong_FD_GE.

	pose proof (lemma_betweennesspreserved _ _ _ _ _ _ Cong_AF_BG Cong_AD_BE Cong_FD_GE BetS_A_F_D) as BetS_B_G_E.

	pose proof (by_def_Cut _ _ _ _ _ BetS_A_F_D BetS_B_F_E nCol_A_D_B nCol_A_D_E) as Cut_AD_BE_F.
	pose proof (by_def_Cut _ _ _ _ _ BetS_A_G_D BetS_B_G_E nCol_A_D_B nCol_A_D_E) as Cut_AD_BE_G.
	pose proof (lemma_twolines _ _ _ _ _ _ Cut_AD_BE_F Cut_AD_BE_G nCol_D_B_E) as eq_F_G.

	assert (Cong A F B F) as Cong_AF_BF by (setoid_rewrite eq_F_G at 1; exact Cong_AG_BF).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AF_BF) as (Cong_FA_FB & _ & _).

	pose proof (lemma_s_Pasch_inner _ _ _ _ _ BetS_E_A_C BetS_E_F_B nCol_E_B_C) as (M & BetS_C_M_F & BetS_A_M_B).

	pose proof (cn_congruencereflexive C M) as Cong_CM_CM.
	pose proof (cn_congruencereflexive M F) as Cong_MF_MF.

	pose proof (lemma_interior5 _ _ _ _ _ _ _ _ BetS_C_M_F BetS_C_M_F Cong_CM_CM Cong_MF_MF Cong_CA_CB Cong_FA_FB) as Cong_MA_MB.

	exists M.
	split.
	exact BetS_A_M_B.
	exact Cong_MA_MB.
Qed.

End Euclid.
