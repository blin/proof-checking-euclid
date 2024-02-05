Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_doublereverse.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.proposition_16.
Require Import ProofCheckingEuclid.proposition_19.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_RightTriangle_legsmallerhypotenuse :
	forall A B C,
	RightTriangle A B C ->
	Lt A B A C /\ Lt B C A C.
Proof.
	intros A B C.
	intros RightTriangle_ABC.

	pose proof (cn_congruencereflexive B A) as Cong_BA_BA.
	pose proof (cn_congruencereverse C A) as Cong_CA_AC.
	pose proof (cn_congruencereverse C B) as Cong_CB_BC.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_ABC) as RightTriangle_CBA.
	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_ABC) as nCol_A_B_C.

	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).

	pose proof (by_def_Triangle _ _ _ nCol_A_B_C) as Triangle_ABC.
	pose proof (by_def_Triangle _ _ _ nCol_A_C_B) as Triangle_ACB.
	pose proof (by_def_Triangle _ _ _ nCol_C_B_A) as Triangle_CBA.

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_A_C) as CongA_BAC_CAB.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_C_B_A) as CongA_CBA_ABC.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_A) as OnRay_BA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_C) as OnRay_BC_C.

	destruct RightTriangle_CBA as (D & BetS_C_B_D & Cong_CB_DB & Cong_CA_DA & _).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_B_D) as (neq_B_D & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_B_D) as neq_D_B.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_B_D) as Col_C_B_D.
	pose proof (by_prop_Col_order _ _ _ Col_C_B_D) as (_ & _ & _ & _ & Col_D_B_C).

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_D) as OnRay_BD_D.

	pose proof (by_prop_Cong_doublereverse _ _ _ _ Cong_CB_DB) as (Cong_BD_BC & _).
	pose proof (by_prop_Cong_doublereverse _ _ _ _ Cong_CA_DA) as (Cong_AD_AC & _).

	assert (~ Col A B D) as n_Col_A_B_D.
	{
		intro Col_A_B_D.

		pose proof (by_prop_Col_order _ _ _ Col_A_B_D) as (_ & _ & _ & _ & Col_D_B_A).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_B_C Col_D_B_A neq_D_B) as Col_B_C_A.
		pose proof (by_prop_Col_order _ _ _ Col_B_C_A) as (_ & _ & Col_A_B_C & _ & _).

		pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_C) as n_Col_A_B_C.

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_A_B_D) as nCol_A_B_D.

	pose proof (
		by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_BA_A OnRay_BD_D OnRay_BA_A OnRay_BC_C Cong_BA_BA Cong_BD_BC Cong_AD_AC nCol_A_B_D
	) as CongA_ABD_ABC.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ABD_ABC) as CongA_ABC_ABD.

	pose proof (proposition_16 _ _ _ _ Triangle_ACB BetS_C_B_D) as (LtA_CAB_ABD & LtA_BCA_ABD).

	pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_CAB_ABD CongA_ABC_ABD) as LtA_CAB_ABC.
	pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_BCA_ABD CongA_ABC_ABD) as LtA_BCA_ABC.
	pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_CAB_ABC CongA_BAC_CAB) as LtA_BAC_ABC.
	pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_BAC_ABC CongA_CBA_ABC) as LtA_BAC_CBA.

	pose proof (proposition_19 _ _ _ Triangle_ABC LtA_BCA_ABC) as Lt_AB_AC.
	pose proof (proposition_19 _ _ _ Triangle_CBA LtA_BAC_CBA) as Lt_CB_CA.

	pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_CB_CA Cong_CB_BC) as Lt_BC_CA.
	pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_BC_CA Cong_CA_AC) as Lt_BC_AC.

	split.
	exact Lt_AB_AC.
	exact Lt_BC_AC.
Qed.

End Euclid.
