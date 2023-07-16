Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_def_LtA.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_TogetherGreater.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_isosceles.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence_smaller.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.proposition_05.
Require Import ProofCheckingEuclid.proposition_19.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.


Lemma proposition_20 :
	forall A B C,
	Triangle A B C ->
	TogetherGreater B A A C B C.
Proof.
	intros A B C.
	intros Triangle_ABC.

	pose proof (lemma_s_ncol_triangle _ _ _ Triangle_ABC) as nCol_A_B_C.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (_ & _ & _ & neq_B_A & neq_C_B & neq_C_A).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & _ & _ & _ & _).

	pose proof (lemma_extension _ _ _ _ neq_B_A neq_C_A) as (D & BetS_B_A_D & Cong_AD_CA).

	pose proof (cn_congruencereflexive D B) as Cong_DB_DB.
	pose proof (cn_congruencereflexive D C) as Cong_DC_DC.
	pose proof (cn_congruencereflexive B C) as Cong_BC_BC.

	pose proof (lemma_betweennotequal _ _ _ BetS_B_A_D) as (neq_A_D & _ & neq_B_D).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_D) as neq_D_A.
	pose proof (lemma_inequalitysymmetric _ _ neq_B_D) as neq_D_B.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_D) as BetS_D_A_B.

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_D_A_B neq_D_A) as OnRay_DA_B.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_AD_CA) as (_ & _ & Cong_AD_AC).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_A_D) as Col_B_A_D.
	pose proof (lemma_collinearorder _ _ _ Col_B_A_D) as (Col_A_B_D & _ & _ & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_A_C Col_B_A_D neq_B_D) as nCol_B_D_C.
	pose proof (lemma_NCorder _ _ _ nCol_B_D_C) as (_ & _ & _ & nCol_B_C_D & nCol_C_D_B).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_B_C Col_A_B_D neq_A_D) as nCol_A_D_C.
	pose proof (lemma_NCorder _ _ _ nCol_A_D_C) as (_ & nCol_D_C_A & _ & nCol_A_C_D & _).

	pose proof (lemma_NCdistinct _ _ _ nCol_A_D_C) as (_ & neq_D_C & _ & _ & neq_C_D & _).

	pose proof (lemma_equalanglesreflexive _ _ _ nCol_D_C_A) as CongA_DCA_DCA.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_C_D_B) as CongA_CDB_BDC.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_C_D) as CongA_BCD_DCB.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_B) as OnRay_CB_B.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_D) as OnRay_CD_D.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_D_B) as OnRay_DB_B.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_D_C) as OnRay_DC_C.

	pose proof (by_def_Triangle _ _ _ nCol_A_D_C) as Triangle_ADC.
	pose proof (by_def_Triangle _ _ _ nCol_B_C_D) as Triangle_BCD.

	pose proof (by_def_isosceles _ _ _ Triangle_ADC Cong_AD_AC) as isosceles_A_D_C.
	pose proof (proposition_05 _ _ _ isosceles_A_D_C) as CongA_ADC_ACD.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_C_D) as CongA_ACD_DCA.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_ADC_ACD CongA_ACD_DCA) as CongA_ADC_DCA.

	pose proof (by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_DA_B OnRay_DC_C OnRay_DB_B OnRay_DC_C Cong_DB_DB Cong_DC_DC Cong_BC_BC nCol_A_D_C) as CongA_ADC_BDC.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_ADC_BDC) as CongA_BDC_ADC.

	pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_D_A_B OnRay_CD_D OnRay_CB_B CongA_DCA_DCA) as LtA_DCA_DCB.
	pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_DCA_DCB CongA_ADC_DCA) as LtA_ADC_DCB.
	pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_ADC_DCB CongA_BDC_ADC) as LtA_BDC_DCB.
	pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_BDC_DCB CongA_CDB_BDC) as LtA_CDB_DCB.
	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_CDB_DCB CongA_BCD_DCB) as LtA_CDB_BCD.

	pose proof (proposition_19 _ _ _ Triangle_BCD LtA_CDB_BCD) as Lt_BC_BD.

	pose proof (by_def_TogetherGreater _ _ _ _ _ _ _ BetS_B_A_D Cong_AD_AC Lt_BC_BD) as TogetherGreater_BA_AC_BC.

	exact TogetherGreater_BA_AC_BC.
Qed.

End Euclid.
