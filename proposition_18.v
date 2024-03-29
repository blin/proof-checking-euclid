Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_LtA.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_isosceles.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_LtA_transitive.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.proposition_03.
Require Import ProofCheckingEuclid.proposition_05.
Require Import ProofCheckingEuclid.proposition_16.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_18 :
	forall A B C,
	Triangle A B C ->
	Lt A B A C ->
	LtA B C A A B C.
Proof.
	intros A B C.
	intros Triangle_ABC.
	intros Lt_AB_AC.

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_ABC) as nCol_A_B_C.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (_ & neq_B_C & _ & neq_B_A & neq_C_B & neq_C_A).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (_ & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & _).

	pose proof (cn_congruencereflexive A C) as Cong_AC_AC.
	pose proof (proposition_03 _ _ _ _ _ _ Lt_AB_AC Cong_AC_AC) as (D & BetS_A_D_C & Cong_AD_AB).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_D_C) as (neq_D_C & neq_A_D & _).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_D_C) as Col_A_D_C.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_C) as BetS_C_D_A.

	pose proof (by_prop_neq_symmetric _ _ neq_A_D) as neq_D_A.
	pose proof (by_prop_neq_symmetric _ _ neq_D_C) as neq_C_D.

	pose proof (by_prop_Col_order _ _ _ Col_A_D_C) as (_ & _ & Col_C_A_D & Col_A_C_D & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_C_A_B Col_C_A_D neq_C_D) as nCol_C_D_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_C_D_B) as (_ & _ & nCol_B_C_D & _ & _).
	pose proof (by_def_Triangle _ _ _ nCol_B_C_D) as Triangle_BCD.

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_C_B Col_A_C_D neq_A_D) as nCol_A_D_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_D_B) as (_ & _ & _ & nCol_A_B_D & _).
	pose proof (by_def_Triangle _ _ _ nCol_A_D_B) as Triangle_ADB.

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_D_B) as CongA_ADB_BDA.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_C_A) as CongA_BCA_ACB.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_A) as OnRay_BA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_C) as OnRay_BC_C.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_B) as OnRay_CB_B.
	pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_C_D_A neq_C_A) as OnRay_CA_D.

	pose proof (by_prop_CongA_reflexive _ _ _ nCol_A_C_B) as CongA_ACB_ACB.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_ACB_ACB OnRay_CA_D OnRay_CB_B) as CongA_ACB_DCB.

	pose proof (by_def_isosceles _ _ _ Triangle_ADB Cong_AD_AB) as isosceles_A_D_B.
	pose proof (proposition_05 _ _ _ isosceles_A_D_B) as CongA_ADB_ABD.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ADB_ABD) as CongA_ABD_ADB.
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_A_B_D) as CongA_ABD_ABD.

	pose proof (proposition_16 _ _ _ _ Triangle_BCD BetS_C_D_A) as (_ & LtA_DCB_BDA).

	pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_DCB_BDA CongA_ACB_DCB) as LtA_ACB_BDA.
	pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_ACB_BDA CongA_ADB_BDA) as LtA_ACB_ADB.
	pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_ACB_ADB CongA_ABD_ADB) as LtA_ACB_ABD.
	pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_ACB_ABD CongA_BCA_ACB) as LtA_BCA_ABD.
	pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_A_D_C OnRay_BA_A OnRay_BC_C CongA_ABD_ABD) as LtA_ABD_ABC.
	pose proof (by_prop_LtA_transitive _ _ _ _ _ _ _ _ _ LtA_BCA_ABD LtA_ABD_ABC) as LtA_BCA_ABC.

	exact LtA_BCA_ABC.
Qed.

End Euclid.
