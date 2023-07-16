Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_def_Midpoint.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NChelper.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennesspreserved.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_oppositesidesymmetric.
Require Import ProofCheckingEuclid.lemma_parallelflip.
Require Import ProofCheckingEuclid.lemma_pointreflectionisometry.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.proposition_10.
Require Import ProofCheckingEuclid.proposition_27.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_31 :
	forall A B C D,
	BetS B D C ->
	nCol B C A ->
	exists X Y Z, BetS X A Y /\ CongA Y A D A D B /\ CongA Y A D B D A /\ CongA D A Y B D A /\ CongA X A D A D C /\ CongA X A D C D A /\ CongA D A X C D A /\ Par X Y B C /\ Cong X A D C /\ Cong A Y B D /\ Cong A Z Z D /\ Cong X Z Z C /\ Cong B Z Z Y /\ BetS X Z C /\ BetS B Z Y /\ BetS A Z D.
Proof.
	intros A B C D.
	intros BetS_B_D_C.
	intros nCol_B_C_A.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq D D) as eq_D_D by (reflexivity).

	pose proof (cn_congruencereverse A D) as Cong_AD_DA.

	pose proof (by_def_Col_from_eq_A_C A D A eq_A_A) as Col_A_D_A.
	pose proof (by_def_Col_from_eq_B_C B D D eq_D_D) as Col_B_D_D.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_D_C) as BetS_C_D_B.
	pose proof (lemma_betweennotequal _ _ _ BetS_B_D_C) as (_ & neq_B_D & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_B_D_C) as (neq_D_C & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_B_D) as neq_D_B.
	pose proof (lemma_inequalitysymmetric _ _ neq_D_C) as neq_C_D.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_D_C) as Col_B_D_C.
	pose proof (lemma_collinearorder _ _ _ Col_B_D_C) as (Col_D_B_C & Col_D_C_B & Col_C_B_D & Col_B_C_D & Col_C_D_B).

	pose proof (lemma_NCdistinct _ _ _ nCol_B_C_A) as (neq_B_C & neq_C_A & neq_B_A & neq_C_B & neq_A_C & neq_A_B).
	pose proof (lemma_NCorder _ _ _ nCol_B_C_A) as (nCol_C_B_A & nCol_C_A_B & nCol_A_B_C & nCol_B_A_C & nCol_A_C_B).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_C_A Col_B_C_D neq_B_D) as nCol_B_D_A.
	pose proof (lemma_NCdistinct _ _ _ nCol_B_D_A) as (_ & neq_D_A & _ & _ & neq_A_D & _).
	pose proof (lemma_NCorder _ _ _ nCol_B_D_A) as (nCol_D_B_A & nCol_D_A_B & nCol_A_B_D & nCol_B_A_D & nCol_A_D_B).

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_D_A) as CongA_BDA_ADB.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_D_B) as CongA_ADB_BDA.

	pose proof (proposition_10 _ _ neq_A_D) as (M & BetS_A_M_D & Cong_MA_MD).

	assert (eq M M) as eq_M_M by (reflexivity).

	pose proof (by_def_Col_from_eq_A_C A M A eq_A_A) as Col_A_M_A.
	pose proof (by_def_Col_from_eq_B_C B M M eq_M_M) as Col_B_M_M.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_M_D) as BetS_D_M_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_M_D) as (_ & neq_A_M & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_M_D) as (neq_M_D & _ & _).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_M_D) as Col_A_M_D.
	pose proof (lemma_collinearorder _ _ _ Col_A_M_D) as (Col_M_A_D & Col_M_D_A & Col_D_A_M & Col_A_D_M & Col_D_M_A).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_MA_MD) as Cong_MD_MA.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_MD_MA) as (_ & Cong_DM_MA & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_MA_MD) as (_ & Cong_AM_MD & _).

	pose proof (lemma_NChelper _ _ _ _ _ nCol_B_D_A Col_B_D_C Col_B_D_D neq_C_D) as nCol_C_D_A.
	pose proof (lemma_NCorder _ _ _ nCol_C_D_A) as (nCol_D_C_A & nCol_D_A_C & nCol_A_C_D & nCol_C_A_D & nCol_A_D_C).
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_C_D_A) as CongA_CDA_ADC.

	pose proof (lemma_NChelper _ _ _ _ _ nCol_A_D_C Col_A_D_A Col_A_D_M neq_A_M) as nCol_A_M_C.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_M_C) as (_ & neq_M_C & _ & _ & neq_C_M & _).
	pose proof (lemma_NCorder _ _ _ nCol_A_M_C) as (nCol_M_A_C & nCol_M_C_A & nCol_C_A_M & nCol_A_C_M & nCol_C_M_A).

	pose proof (lemma_NChelper _ _ _ _ _ nCol_A_D_B Col_A_D_A Col_A_D_M neq_A_M) as nCol_A_M_B.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_M_B) as (_ & neq_M_B & _ & _ & neq_B_M & _).
	pose proof (lemma_NCorder _ _ _ nCol_A_M_B) as (nCol_M_A_B & nCol_M_B_A & nCol_B_A_M & nCol_A_B_M & nCol_B_M_A).

	pose proof (by_def_Midpoint _ _ _ BetS_A_M_D Cong_AM_MD) as Midpoint_A_M_D.
	pose proof (by_def_Midpoint _ _ _ BetS_D_M_A Cong_DM_MA) as Midpoint_D_M_A.

	pose proof (lemma_extension _ _ _ _ neq_C_M neq_M_C) as (E & BetS_C_M_E & Cong_ME_MC).

	assert (eq E E) as eq_E_E by (reflexivity).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_M_E) as BetS_E_M_C.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_ME_MC) as Cong_MC_ME.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_MC_ME) as (_ & Cong_CM_ME & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_CM_ME) as (Cong_MC_EM & _ & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_MC_EM) as Cong_EM_MC.

	pose proof (by_def_Midpoint _ _ _ BetS_C_M_E Cong_CM_ME) as Midpoint_C_M_E.
	pose proof (by_def_Midpoint _ _ _ BetS_E_M_C Cong_EM_MC) as Midpoint_E_M_C.

	pose proof (lemma_extension _ _ _ _ neq_B_M neq_M_B) as (F & BetS_B_M_F & Cong_MF_MB).

	assert (eq F F) as eq_F_F by (reflexivity).

	pose proof (by_def_Col_from_eq_B_C F A A eq_A_A) as Col_F_A_A.

	pose proof (lemma_betweennotequal _ _ _ BetS_B_M_F) as (neq_M_F & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_M_F) as neq_F_M.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_M_F) as Col_B_M_F.
	pose proof (lemma_collinearorder _ _ _ Col_B_M_F) as (Col_M_B_F & Col_M_F_B & Col_F_B_M & Col_B_F_M & Col_F_M_B).

	pose proof (lemma_congruenceflip _ _ _ _ Cong_MF_MB) as (_ & _ & Cong_MF_BM).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_MF_BM) as Cong_BM_MF.

	pose proof (by_def_Midpoint _ _ _ BetS_B_M_F Cong_BM_MF) as Midpoint_B_M_F.

	pose proof (lemma_NChelper _ _ _ _ _ nCol_B_M_A Col_B_M_F Col_B_M_M neq_F_M) as nCol_F_M_A.
	pose proof (lemma_NCorder _ _ _ nCol_F_M_A) as (nCol_M_F_A & nCol_M_A_F & nCol_A_F_M & nCol_F_A_M & nCol_A_M_F).

	pose proof (lemma_NChelper _ _ _ _ _ nCol_A_M_F Col_A_M_A Col_A_M_D neq_A_D) as nCol_A_D_F.
	pose proof (lemma_NCorder _ _ _ nCol_A_D_F) as (nCol_D_A_F & nCol_D_F_A & nCol_F_A_D & nCol_A_F_D & nCol_F_D_A).

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_F_A_D) as CongA_FAD_DAF.

	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_B_M_F Midpoint_D_M_A neq_B_D) as Cong_BD_FA.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_D_M_A Midpoint_C_M_E neq_D_C) as Cong_DC_AE.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_B_M_F Midpoint_C_M_E neq_B_C) as Cong_BC_FE.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_B_M_F Midpoint_A_M_D neq_B_A) as Cong_BA_FD.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_BD_FA) as (Cong_DB_AF & _ & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_DB_AF) as Cong_AF_DB.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_DB_AF) as (_ & Cong_BD_AF & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BD_AF) as Cong_AF_BD.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_DC_AE) as (_ & _ & Cong_DC_EA).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_DC_EA) as Cong_EA_DC.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BA_FD) as Cong_FD_BA.

	pose proof (lemma_betweennesspreserved _ _ _ _ _ _ Cong_BD_FA Cong_BC_FE Cong_DC_AE BetS_B_D_C) as BetS_F_A_E.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_A_E) as BetS_E_A_F.
	pose proof (lemma_betweennotequal _ _ _ BetS_E_A_F) as (neq_A_F & _ & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_A_F) as (_ & neq_E_A & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_E_A) as neq_A_E.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_A_F) as Col_E_A_F.
	pose proof (lemma_collinearorder _ _ _ Col_E_A_F) as (Col_A_E_F & Col_A_F_E & Col_F_E_A & Col_E_F_A & Col_F_A_E).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_F_D Col_A_F_E neq_A_E) as nCol_A_E_D.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_E_D) as (_ & neq_E_D & _ & _ & neq_D_E & _).
	pose proof (lemma_NCorder _ _ _ nCol_A_E_D) as (nCol_E_A_D & nCol_E_D_A & nCol_D_A_E & nCol_A_D_E & nCol_D_E_A).
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_D_A_E) as CongA_DAE_EAD.

	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_E_M_C Midpoint_D_M_A neq_E_D) as Cong_ED_CA.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_A_M_D Midpoint_E_M_C neq_A_E) as Cong_AE_DC.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_D_C) as OnRay_DC_C.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_D_B) as OnRay_DB_B.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_D_A) as OnRay_DA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_A_D) as OnRay_AD_D.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_A_E) as OnRay_AE_E.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_A_F) as OnRay_AF_F.

	pose proof (by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_AF_F OnRay_AD_D OnRay_DB_B OnRay_DA_A Cong_AF_DB Cong_AD_DA Cong_FD_BA nCol_F_A_D) as CongA_FAD_BDA.
	pose proof (by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_AE_E OnRay_AD_D OnRay_DC_C OnRay_DA_A Cong_AE_DC Cong_AD_DA Cong_ED_CA nCol_E_A_D) as CongA_EAD_CDA.

	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_FAD_BDA CongA_BDA_ADB) as CongA_FAD_ADB.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_FAD_ADB) as CongA_ADB_FAD.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_ADB_FAD CongA_FAD_DAF) as CongA_ADB_DAF.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_ADB_DAF) as CongA_DAF_ADB.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_DAF_ADB CongA_ADB_BDA) as CongA_DAF_BDA.

	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_EAD_CDA CongA_CDA_ADC) as CongA_EAD_ADC.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_DAE_EAD CongA_EAD_CDA) as CongA_DAE_CDA.

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_B_M_F Col_A_D_M nCol_A_D_B) as OppositeSide_B_AD_F.
	pose proof (lemma_oppositesidesymmetric _ _ _ _ OppositeSide_B_AD_F) as OppositeSide_F_AD_B.

	pose proof (proposition_27 _ _ _ _ _ _ BetS_F_A_E BetS_C_D_B CongA_FAD_ADB OppositeSide_F_AD_B) as Par_FE_CB.
	pose proof (lemma_parallelflip _ _ _ _ Par_FE_CB) as (_ & _ & Par_EF_BC).

	exists E, F, M.
	split.
	exact BetS_E_A_F.
	split.
	exact CongA_FAD_ADB.
	split.
	exact CongA_FAD_BDA.
	split.
	exact CongA_DAF_BDA.
	split.
	exact CongA_EAD_ADC.
	split.
	exact CongA_EAD_CDA.
	split.
	exact CongA_DAE_CDA.
	split.
	exact Par_EF_BC.
	split.
	exact Cong_EA_DC.
	split.
	exact Cong_AF_BD.
	split.
	exact Cong_AM_MD.
	split.
	exact Cong_EM_MC.
	split.
	exact Cong_BM_MF.
	split.
	exact BetS_E_M_C.
	split.
	exact BetS_B_M_F.
	exact BetS_A_M_D.
Qed.

End Euclid.
