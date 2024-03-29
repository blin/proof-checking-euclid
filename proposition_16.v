Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_InAngle.
Require Import ProofCheckingEuclid.by_def_LtA_from_InAngle.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_doublereverse.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_s_Pasch_inner.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_10.
Require Import ProofCheckingEuclid.proposition_15.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_16_LtA_BAC_ACD :
	forall A B C D,
	Triangle A B C ->
	BetS B C D ->
	LtA B A C A C D.
Proof.
	intros A B C D.
	intros Triangle_ABC.
	intros BetS_B_C_D.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_C_D) as (neq_C_D & _ & neq_B_D).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_C_D) as Col_B_C_D.

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_ABC) as nCol_A_B_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & _ & _ & nCol_A_C_B & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & _ & neq_A_C & _ & _ & neq_C_A).

	pose proof (proposition_10 _ _ neq_A_C) as (E & BetS_A_E_C & Cong_EA_EC).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_E_C) as (neq_E_C & neq_A_E & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_C) as BetS_C_E_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_E_A) as (_ & neq_C_E & _).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_E_C) as Col_A_E_C.
	pose proof (by_prop_Col_order _ _ _ Col_A_E_C) as (Col_E_A_C & _ & _ & Col_A_C_E & _).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_C_B Col_A_C_E neq_A_E) as nCol_A_E_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_E_B) as (nCol_E_A_B & _ & nCol_B_A_E & _ & nCol_B_E_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_E_B) as (_ & neq_E_B & _ & _ & neq_B_E & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_E_A_B Col_E_A_C neq_E_C) as nCol_E_C_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_E_C_B) as (_ & _ & nCol_B_E_C & nCol_E_B_C & _).

	pose proof (lemma_extension _ _ _ _ neq_B_E neq_E_B) as (F & BetS_B_E_F & Cong_EF_EB).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_E_F) as (neq_E_F & _ & neq_B_F).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_E_F) as Col_B_E_F.
	pose proof (by_prop_Col_order _ _ _ Col_B_E_F) as (Col_E_B_F & _ & _ & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_E_B_C Col_E_B_F neq_E_F) as nCol_E_F_C.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_E_F_C) as (_ & _ & _ & _ & neq_C_F & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_E_F_C) as (_ & _ & _ & nCol_E_C_F & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_E_C Col_B_E_F neq_B_F) as nCol_B_F_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_B_F_C) as (_ & _ & _ & nCol_B_C_F & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_C_F Col_B_C_D neq_B_D) as nCol_B_D_F.
	pose proof (by_prop_nCol_order _ _ _ nCol_B_D_F) as (_ & _ & _ & nCol_B_F_D & _).

	pose proof (by_prop_Cong_doublereverse _ _ _ _ Cong_EF_EB) as (Cong_BE_FE & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BE_FE) as (Cong_EB_EF & _ & _).

	pose proof (lemma_s_Pasch_inner _ _ _ _ _ BetS_B_C_D BetS_B_E_F nCol_B_F_D) as (H & BetS_D_H_E & BetS_C_H_F).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_H_E) as BetS_E_H_D.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_A_B) as OnRay_AB_B.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_A) as OnRay_CA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_D) as OnRay_CD_D.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_F) as OnRay_CF_F.
	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_C_E_A neq_C_E) as OnRay_CE_A.
	pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_A_E_C neq_A_C) as OnRay_AC_E.
	pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_C_H_F neq_C_F) as OnRay_CF_H.

	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_CE_A) as OnRay_CA_E.

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_E_B) as CongA_AEB_BEA.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_A_E) as CongA_BAE_EAB.
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_B_A_C) as CongA_BAC_BAC.
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_E_C_F) as CongA_ECF_ECF.

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_BAC_BAC OnRay_AB_B OnRay_AC_E) as CongA_BAC_BAE.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_ECF_ECF OnRay_CE_A OnRay_CF_F) as CongA_ECF_ACF.

	pose proof (proposition_15 _ _ _ _ _ BetS_B_E_F BetS_A_E_C nCol_B_E_A) as (CongA_BEA_CEF & _).
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_AEB_BEA CongA_BEA_CEF) as CongA_AEB_CEF.
	pose proof (proposition_04 _ _ _ _ _ _ Cong_EA_EC Cong_EB_EF CongA_AEB_CEF) as (_ & CongA_EAB_ECF & _).
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_BAC_BAE CongA_BAE_EAB) as CongA_BAC_EAB.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_BAC_EAB CongA_EAB_ECF) as CongA_BAC_ECF.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_BAC_ECF CongA_ECF_ACF) as CongA_BAC_ACF.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_BAC_ACF OnRay_CA_A OnRay_CF_H) as CongA_BAC_ACH.

	pose proof (by_def_InAngle _ _ _ _ _ _ OnRay_CA_E OnRay_CD_D BetS_E_H_D) as InAngle_ACD_H.
	pose proof (by_def_LtA_from_InAngle _ _ _ _ _ _ _ InAngle_ACD_H CongA_BAC_ACH) as LtA_BAC_ACD.

	exact LtA_BAC_ACD.
Qed.

Lemma proposition_16_LtA_CBA_ACD :
	forall A B C D,
	Triangle A B C ->
	BetS B C D ->
	LtA C B A A C D.
Proof.
	intros A B C D.
	intros Triangle_ABC.
	intros BetS_B_C_D.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_C_D) as (neq_C_D & neq_B_C & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_C_D) as BetS_D_C_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_D_C_B) as (neq_C_B & _ & _).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_C_D) as Col_B_C_D.
	pose proof (by_prop_Col_order _ _ _ Col_B_C_D) as (Col_C_B_D & _ & _ & _ & _).

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_ABC) as nCol_A_B_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (_ & nCol_B_C_A & nCol_C_A_B & _ & nCol_C_B_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (_ & _ & neq_A_C & neq_B_A & _ & _).

	pose proof (proposition_10 _ _ neq_B_C) as (E & BetS_B_E_C & Cong_EB_EC).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_E_C) as BetS_C_E_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_E_C) as (neq_E_C & neq_B_E & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_E_B) as (_ & neq_C_E & _).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_E_C) as Col_B_E_C.
	pose proof (by_prop_Col_order _ _ _ Col_B_E_C) as (Col_E_B_C & _ & _ & Col_B_C_E & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_C_A Col_B_C_E neq_B_E) as nCol_B_E_A.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_E_A) as (_ & neq_E_A & _ & _ & neq_A_E & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_B_E_A) as (_ & nCol_E_A_B & nCol_A_B_E & _ & nCol_A_E_B).

	pose proof (lemma_extension _ _ _ _ neq_A_E neq_E_A) as (F & BetS_A_E_F & Cong_EF_EA).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_E_F) as (neq_E_F & _ & neq_A_F).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_E_F) as Col_A_E_F.
	pose proof (by_prop_Col_order _ _ _ Col_A_E_F) as (Col_E_A_F & Col_E_F_A & _ & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_E_A_B Col_E_A_F neq_E_F) as nCol_E_F_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_E_F_B) as (_ & _ & _ & nCol_E_B_F & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_E_B_F Col_E_B_C neq_E_C) as nCol_E_C_F.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_E_C_F) as (_ & neq_C_F & _ & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_E_C_F) as (_ & _ & _ & nCol_E_F_C & _).

	pose proof (by_prop_Cong_doublereverse _ _ _ _ Cong_EF_EA) as (Cong_AE_FE & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AE_FE) as (Cong_EA_EF & _ & _).

	pose proof (postulate_Euclid2 _ _ neq_A_C) as (G & BetS_A_C_G).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_G) as BetS_G_C_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_C_G) as (neq_C_G & _ & neq_A_G).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_C_G) as Col_A_C_G.
	pose proof (by_prop_Col_order _ _ _ Col_A_C_G) as (Col_C_A_G & _ & _ & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_E_F_C Col_E_F_A neq_E_A) as nCol_E_A_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_E_A_C) as (_ & nCol_A_C_E & _ & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_C_E Col_A_C_G neq_A_G) as nCol_A_G_E.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_G_E) as (_ & _ & _ & nCol_A_E_G & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_E_G Col_A_E_F neq_A_F) as nCol_A_F_G.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_F_G) as (_ & _ & nCol_G_A_F & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_C_A_B Col_C_A_G neq_C_G) as nCol_C_G_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_C_G_B) as (nCol_G_C_B & _ & _ & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_C_B_A Col_C_B_D neq_C_D) as nCol_C_D_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_C_D_A) as (nCol_D_C_A & _ & _ & _ & _).

	pose proof (lemma_s_Pasch_inner _ _ _ _ _ BetS_A_C_G BetS_A_E_F nCol_A_F_G) as (H & BetS_G_H_E & BetS_C_H_F).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_H_E) as BetS_E_H_G.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_H_F) as (_ & neq_C_H & _).

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_A) as OnRay_BA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_B) as OnRay_CB_B.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_G) as OnRay_CG_G.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_F) as OnRay_CF_F.
	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_C_E_B neq_C_E) as OnRay_CE_B.
	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_C_H_F neq_C_H) as OnRay_CH_F.
	pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_B_E_C neq_B_C) as OnRay_BC_E.

	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_CE_B) as OnRay_CB_E.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_CH_F) as OnRay_CF_H.

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_B_E) as CongA_ABE_EBA.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_E_A) as CongA_BEA_AEB.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_C_B_A) as CongA_CBA_ABC.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_D_C_A) as CongA_DCA_ACD.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_G_C_B) as CongA_GCB_BCG.
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_A_B_C) as CongA_ABC_ABC.
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_E_C_F) as CongA_ECF_ECF.

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_ABC_ABC OnRay_BA_A OnRay_BC_E) as CongA_ABC_ABE.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_ECF_ECF OnRay_CE_B OnRay_CF_F) as CongA_ECF_BCF.

	pose proof (proposition_15 _ _ _ _ _ BetS_A_E_F BetS_B_E_C nCol_A_E_B) as (CongA_AEB_CEF & _).
	pose proof (proposition_15 _ _ _ _ _ BetS_G_C_A BetS_B_C_D nCol_G_C_B) as (CongA_GCB_DCA & _).
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_BEA_AEB CongA_AEB_CEF) as CongA_BEA_CEF.
	pose proof (proposition_04 _ _ _ _ _ _ Cong_EB_EC Cong_EA_EF CongA_BEA_CEF) as (_ & CongA_EBA_ECF & _).
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_ABE CongA_ABE_EBA) as CongA_ABC_EBA.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_EBA CongA_EBA_ECF) as CongA_ABC_ECF.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_ECF CongA_ECF_BCF) as CongA_ABC_BCF.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_GCB_DCA CongA_DCA_ACD) as CongA_GCB_ACD.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_GCB_ACD) as CongA_ACD_GCB.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_ABC_BCF OnRay_CB_B OnRay_CF_H) as CongA_ABC_BCH.

	pose proof (by_def_InAngle _ _ _ _ _ _ OnRay_CB_E OnRay_CG_G BetS_E_H_G) as InAngle_BCG_H.
	pose proof (by_def_LtA_from_InAngle _ _ _ _ _ _ _ InAngle_BCG_H CongA_ABC_BCH) as LtA_ABC_BCG.
	pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_ABC_BCG CongA_GCB_BCG) as LtA_ABC_GCB.
	pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_ABC_GCB CongA_ACD_GCB) as LtA_ABC_ACD.
	pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_ABC_ACD CongA_CBA_ABC) as LtA_CBA_ACD.

	exact LtA_CBA_ACD.
Qed.

Lemma proposition_16 :
	forall A B C D,
	Triangle A B C ->
	BetS B C D ->
	LtA B A C A C D /\ LtA C B A A C D.
Proof.
	intros A B C D.
	intros Triangle_ABC.
	intros BetS_B_C_D.

	pose proof (proposition_16_LtA_BAC_ACD _ _ _ _ Triangle_ABC BetS_B_C_D) as LtA_BAC_ACD.
	pose proof (proposition_16_LtA_CBA_ACD _ _ _ _ Triangle_ABC BetS_B_C_D) as LtA_CBA_ACD.

	split.
	exact LtA_BAC_ACD.
	exact LtA_CBA_ACD.
Qed.

End Euclid.
