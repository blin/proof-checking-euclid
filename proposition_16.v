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
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_lta.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
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

	pose proof (lemma_betweennotequal _ _ _ BetS_B_C_D) as (neq_C_D & _ & neq_B_D).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_C_D) as BetS_D_C_B.
	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_B_C_D) as Col_B_C_D.

	pose proof (lemma_s_ncol_triangle _ _ _ Triangle_ABC) as nCol_A_B_C.
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & _ & _ & nCol_A_C_B & _).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & _ & neq_A_C & _ & _ & neq_C_A).

	pose proof (proposition_10 A C neq_A_C) as (E & BetS_A_E_C & Cong_EA_EC).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_E_C) as (neq_E_C & neq_A_E & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_C) as BetS_C_E_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_C_E_A) as (_ & neq_C_E & _).
	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_E_C) as Col_A_E_C.
	pose proof (lemma_collinearorder _ _ _ Col_A_E_C) as (Col_E_A_C & _ & _ & Col_A_C_E & _).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_C_B Col_A_C_E neq_A_E) as nCol_A_E_B.
	pose proof (lemma_NCorder _ _ _ nCol_A_E_B) as (nCol_E_A_B & _ & nCol_B_A_E & _ & nCol_B_E_A).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_E_B) as (_ & neq_E_B & _ & _ & neq_B_E & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_E_A_B Col_E_A_C neq_E_C) as nCol_E_C_B.
	pose proof (lemma_NCorder _ _ _ nCol_E_C_B) as (_ & _ & nCol_B_E_C & nCol_E_B_C & _).

	pose proof (lemma_extension _ _ _ _ neq_B_E neq_E_B) as (F & BetS_B_E_F & Cong_EF_EB).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_E_F) as BetS_F_E_B.
	pose proof (lemma_betweennotequal _ _ _ BetS_B_E_F) as (neq_E_F & _ & neq_B_F).
	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_B_E_F) as Col_B_E_F.
	pose proof (lemma_collinearorder _ _ _ Col_B_E_F) as (Col_E_B_F & _ & _ & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_E_B_C Col_E_B_F neq_E_F) as nCol_E_F_C.
	pose proof (lemma_NCdistinct _ _ _ nCol_E_F_C) as (_ & _ & _ & _ & neq_C_F & _).
	pose proof (lemma_NCorder _ _ _ nCol_E_F_C) as (_ & _ & _ & nCol_E_C_F & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_E_C Col_B_E_F neq_B_F) as nCol_B_F_C.
	pose proof (lemma_NCorder _ _ _ nCol_B_F_C) as (_ & _ & _ & nCol_B_C_F & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_C_F Col_B_C_D neq_B_D) as nCol_B_D_F.
	pose proof (lemma_NCorder _ _ _ nCol_B_D_F) as (nCol_D_B_F & _ & _ & _ & _).

	pose proof (lemma_doublereverse _ _ _ _ Cong_EF_EB) as (Cong_BE_FE & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_BE_FE) as (Cong_EB_EF & _ & _).

	pose proof (postulate_Pasch_inner D F B C E BetS_D_C_B BetS_F_E_B nCol_D_B_F) as (H & BetS_D_H_E & BetS_F_H_C).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_H_E) as BetS_E_H_D.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_H_C) as BetS_C_H_F.

	pose proof (lemma_s_onray_assert_ABB _ _ neq_A_B) as OnRay_AB_B.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_C_A) as OnRay_CA_A.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_C_D) as OnRay_CD_D.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_C_F) as OnRay_CF_F.
	pose proof (lemma_s_onray_assert_bets_ABE _ _ _ BetS_C_E_A neq_C_E) as OnRay_CE_A.
	pose proof (lemma_s_onray_assert_bets_AEB _ _ _ BetS_A_E_C neq_A_C) as OnRay_AC_E.
	pose proof (lemma_s_onray_assert_bets_AEB _ _ _ BetS_C_H_F neq_C_F) as OnRay_CF_H.

	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_CE_A) as OnRay_CA_E.

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_E_B) as CongA_AEB_BEA.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_A_E) as CongA_BAE_EAB.
	pose proof (lemma_equalanglesreflexive _ _ _ nCol_B_A_C) as CongA_BAC_BAC.
	pose proof (lemma_equalanglesreflexive _ _ _ nCol_E_C_F) as CongA_ECF_ECF.

	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_BAC_BAC OnRay_AB_B OnRay_AC_E) as CongA_BAC_BAE.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_ECF_ECF OnRay_CE_A OnRay_CF_F) as CongA_ECF_ACF.

	pose proof (proposition_15 B F A C E BetS_B_E_F BetS_A_E_C nCol_B_E_A) as (CongA_BEA_CEF & _).
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_AEB_BEA CongA_BEA_CEF) as CongA_AEB_CEF.
	pose proof (proposition_04 E A B E C F Cong_EA_EC Cong_EB_EF CongA_AEB_CEF) as (_ & CongA_EAB_ECF & _).
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_BAC_BAE CongA_BAE_EAB) as CongA_BAC_EAB.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_BAC_EAB CongA_EAB_ECF) as CongA_BAC_ECF.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_BAC_ECF CongA_ECF_ACF) as CongA_BAC_ACF.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_BAC_ACF OnRay_CA_A OnRay_CF_H) as CongA_BAC_ACH.

	pose proof (lemma_s_lta _ _ _ _ _ _ _ _ _ BetS_E_H_D OnRay_CA_E OnRay_CD_D CongA_BAC_ACH) as LtA_BAC_ACD.

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

	pose proof (lemma_betweennotequal _ _ _ BetS_B_C_D) as (neq_C_D & neq_B_C & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_C_D) as BetS_D_C_B.
	pose proof (lemma_betweennotequal _ _ _ BetS_D_C_B) as (neq_C_B & _ & _).

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_B_C_D) as Col_B_C_D.
	pose proof (lemma_collinearorder _ _ _ Col_B_C_D) as (Col_C_B_D & _ & _ & _ & _).

	pose proof (lemma_s_ncol_triangle _ _ _ Triangle_ABC) as nCol_A_B_C.
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (_ & nCol_B_C_A & nCol_C_A_B & _ & nCol_C_B_A).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (_ & _ & neq_A_C & neq_B_A & _ & _).

	pose proof (proposition_10 B C neq_B_C) as (e & BetS_B_e_C & Cong_eB_eC).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_e_C) as BetS_C_e_B.
	pose proof (lemma_betweennotequal _ _ _ BetS_B_e_C) as (neq_e_C & neq_B_e & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_C_e_B) as (_ & neq_C_e & _).

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_B_e_C) as Col_B_e_C.
	pose proof (lemma_collinearorder _ _ _ Col_B_e_C) as (Col_e_B_C & _ & _ & Col_B_C_e & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_C_A Col_B_C_e neq_B_e) as nCol_B_e_A.
	pose proof (lemma_NCdistinct _ _ _ nCol_B_e_A) as (_ & neq_e_A & _ & _ & neq_A_e & _).
	pose proof (lemma_NCorder _ _ _ nCol_B_e_A) as (_ & nCol_e_A_B & nCol_A_B_e & _ & nCol_A_e_B).

	pose proof (lemma_extension _ _ _ _ neq_A_e neq_e_A) as (f & BetS_A_e_f & Cong_ef_eA).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_e_f) as BetS_f_e_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_e_f) as (neq_e_f & _ & neq_A_f).
	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_e_f) as Col_A_e_f.
	pose proof (lemma_collinearorder _ _ _ Col_A_e_f) as (Col_e_A_f & Col_e_f_A & _ & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_e_A_B Col_e_A_f neq_e_f) as nCol_e_f_B.
	pose proof (lemma_NCorder _ _ _ nCol_e_f_B) as (_ & _ & _ & nCol_e_B_f & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_e_B_f Col_e_B_C neq_e_C) as nCol_e_C_f.
	pose proof (lemma_NCdistinct _ _ _ nCol_e_C_f) as (_ & neq_C_f & _ & _ & _ & _).
	pose proof (lemma_NCorder _ _ _ nCol_e_C_f) as (_ & _ & _ & nCol_e_f_C & _).

	pose proof (lemma_doublereverse _ _ _ _ Cong_ef_eA) as (Cong_Ae_fe & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_Ae_fe) as (Cong_eA_ef & _ & _).

	(* TODO: this doesn't need to be an extension! Replace with euclid 2 *)
	pose proof (postulate_Euclid2 _ _ neq_A_C) as (G & BetS_A_C_G).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_G) as BetS_G_C_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_C_G) as (neq_C_G & _ & neq_A_G).

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_C_G) as Col_A_C_G.
	pose proof (lemma_collinearorder _ _ _ Col_A_C_G) as (Col_C_A_G & _ & _ & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_e_f_C Col_e_f_A neq_e_A) as nCol_e_A_C.
	pose proof (lemma_NCorder _ _ _ nCol_e_A_C) as (_ & nCol_A_C_e & _ & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_C_e Col_A_C_G neq_A_G) as nCol_A_G_e.
	pose proof (lemma_NCorder _ _ _ nCol_A_G_e) as (_ & _ & _ & nCol_A_e_G & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_e_G Col_A_e_f neq_A_f) as nCol_A_f_G.
	pose proof (lemma_NCorder _ _ _ nCol_A_f_G) as (_ & _ & nCol_G_A_f & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_C_A_B Col_C_A_G neq_C_G) as nCol_C_G_B.
	pose proof (lemma_NCorder _ _ _ nCol_C_G_B) as (nCol_G_C_B & _ & _ & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_C_B_A Col_C_B_D neq_C_D) as nCol_C_D_A.
	pose proof (lemma_NCorder _ _ _ nCol_C_D_A) as (nCol_D_C_A & _ & _ & _ & _).

	pose proof (postulate_Pasch_inner G f A C e BetS_G_C_A BetS_f_e_A nCol_G_A_f) as (h & BetS_G_h_e & BetS_f_h_C).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_h_e) as BetS_e_h_G.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_f_h_C) as BetS_C_h_f.
	pose proof (lemma_betweennotequal _ _ _ BetS_C_h_f) as (_ & neq_C_h & _).

	pose proof (lemma_s_onray_assert_ABB _ _ neq_B_A) as OnRay_BA_A.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_C_B) as OnRay_CB_B.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_C_G) as OnRay_CG_G.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_C_f) as OnRay_Cf_f.
	pose proof (lemma_s_onray_assert_bets_ABE _ _ _ BetS_C_e_B neq_C_e) as OnRay_Ce_B.
	pose proof (lemma_s_onray_assert_bets_ABE _ _ _ BetS_C_h_f neq_C_h) as OnRay_Ch_f.
	pose proof (lemma_s_onray_assert_bets_AEB _ _ _ BetS_B_e_C neq_B_C) as OnRay_BC_e.

	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_Ce_B) as OnRay_CB_e.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_Ch_f) as OnRay_Cf_h.

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_B_e) as CongA_ABe_eBA.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_e_A) as CongA_BeA_AeB.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_C_B_A) as CongA_CBA_ABC.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_D_C_A) as CongA_DCA_ACD.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_G_C_B) as CongA_GCB_BCG.
	pose proof (lemma_equalanglesreflexive _ _ _ nCol_A_B_C) as CongA_ABC_ABC.
	pose proof (lemma_equalanglesreflexive _ _ _ nCol_e_C_f) as CongA_eCf_eCf.

	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_ABC_ABC OnRay_BA_A OnRay_BC_e) as CongA_ABC_ABe.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_eCf_eCf OnRay_Ce_B OnRay_Cf_f) as CongA_eCf_BCf.

	pose proof (proposition_15 A f B C e BetS_A_e_f BetS_B_e_C nCol_A_e_B) as (CongA_AeB_Cef & _).
	pose proof (proposition_15 G A B D C BetS_G_C_A BetS_B_C_D nCol_G_C_B) as (CongA_GCB_DCA & _).
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_BeA_AeB CongA_AeB_Cef) as CongA_BeA_Cef.
	pose proof (proposition_04 e B A e C f Cong_eB_eC Cong_eA_ef CongA_BeA_Cef) as (_ & CongA_eBA_eCf & _).
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_ABC_ABe CongA_ABe_eBA) as CongA_ABC_eBA.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_ABC_eBA CongA_eBA_eCf) as CongA_ABC_eCf.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_ABC_eCf CongA_eCf_BCf) as CongA_ABC_BCf.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_GCB_DCA CongA_DCA_ACD) as CongA_GCB_ACD.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_GCB_ACD) as CongA_ACD_GCB.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_ABC_BCf OnRay_CB_B OnRay_Cf_h) as CongA_ABC_BCh.

	pose proof (lemma_s_lta _ _ _ _ _ _ _ _ _ BetS_e_h_G OnRay_CB_e OnRay_CG_G CongA_ABC_BCh) as LtA_ABC_BCG.
	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_ABC_BCG CongA_GCB_BCG) as LtA_ABC_GCB.
	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_ABC_GCB CongA_ACD_GCB) as LtA_ABC_ACD.
	pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_ABC_ACD CongA_CBA_ABC) as LtA_CBA_ACD.

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
