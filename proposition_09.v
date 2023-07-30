Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_def_InAngle.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_doublereverse.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_OnRay_impliescollinear.
Require Import ProofCheckingEuclid.by_prop_OnRay_neq_A_C.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.proposition_10.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_09 :
	forall A B C,
	nCol B A C ->
	exists X, CongA B A X X A C /\ InAngle B A C X.
Proof.
	intros A B C.
	intros nCol_B_A_C.

	pose proof (by_prop_nCol_order _ _ _ nCol_B_A_C) as (nCol_A_B_C & nCol_A_C_B & _ & _ & _).
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_C) as n_Col_A_B_C.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & _ & neq_A_C & _ & _ & _).

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_A_B) as OnRay_AB_B.

	pose proof (lemma_layoff _ _ _ _ neq_A_C neq_A_B) as (E & OnRay_AC_E & Cong_AE_AB).

	pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_AC_E) as Col_A_C_E.
	pose proof (by_prop_OnRay_neq_A_C _ _ _ OnRay_AC_E) as neq_A_E.

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_C_B Col_A_C_E neq_A_E) as nCol_A_E_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_E_B) as (_ & _ & _ & _ & nCol_B_E_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_E_B) as (_ & _ & _ & _ & neq_B_E & _).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AE_AB) as Cong_AB_AE.

	pose proof (proposition_10 _ _ neq_B_E) as (F & BetS_B_F_E & Cong_FB_FE).

	pose proof (cn_congruencereflexive A F) as Cong_AF_AF.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_F_E) as (_ & neq_B_F & _).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_F_E) as Col_B_F_E.
	pose proof (by_prop_Col_order _ _ _ Col_B_F_E) as (_ & _ & _ & Col_B_E_F & _).

	pose proof (by_def_InAngle _ _ _ _ _ _ OnRay_AB_B OnRay_AC_E BetS_B_F_E) as InAngle_BAC_F.

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_E_A Col_B_E_F neq_B_F) as nCol_B_F_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_B_F_A) as (_ & _ & _ & nCol_B_A_F & _).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_A_F) as (_ & neq_A_F & _ & _ & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_A_F) as OnRay_AF_F.

	pose proof (by_prop_Cong_doublereverse _ _ _ _ Cong_FB_FE) as (Cong_EF_BF & _).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_EF_BF) as Cong_BF_EF.

	pose proof (
		by_def_CongA
		B A F C A F
		_ _ _ _
		OnRay_AB_B
		OnRay_AF_F
		OnRay_AC_E
		OnRay_AF_F
		Cong_AB_AE
		Cong_AF_AF
		Cong_BF_EF
		nCol_B_A_F
	) as CongA_BAF_CAF.

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_BAF_CAF) as CongA_CAF_BAF.
	assert (CongA_CAF_BAF2 := CongA_CAF_BAF).
	destruct CongA_CAF_BAF2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nCol_C_A_F).
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_C_A_F) as CongA_CAF_FAC.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_BAF_CAF CongA_CAF_FAC) as CongA_BAF_FAC.

	exists F.
	split.
	exact CongA_BAF_FAC.
	exact InAngle_BAC_F.
Qed.

End Euclid.
