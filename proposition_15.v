Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_Supp.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_supplements_conga.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_15 :
	forall A B C D E,
	BetS A E B ->
	BetS C E D ->
	nCol A E C ->
	CongA A E C D E B /\ CongA C E B A E D.
Proof.
	intros A B C D E.
	intros BetS_A_E_B.
	intros BetS_C_E_D.
	intros nCol_A_E_C.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_B) as BetS_B_E_A.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_E_D) as BetS_D_E_C.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_E_B) as (neq_E_B & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_E_D) as (neq_E_D & _ & _).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_E_B) as Col_A_E_B.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_E_D) as Col_C_E_D.
	pose proof (by_prop_Col_order _ _ _ Col_A_E_B) as (Col_E_A_B & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_C_E_D) as (Col_E_C_D & _ & _ & _ & _).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_E_C) as (_ & neq_E_C & _ & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_E_C) as (nCol_E_A_C & nCol_E_C_A & _ & _ & _).
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_E_C) as CongA_AEC_CEA.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_E_B) as OnRay_EB_B.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_E_C) as OnRay_EC_C.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_E_D) as OnRay_ED_D.

	pose proof (by_def_Supp _ _ _ _ _ OnRay_EB_B BetS_C_E_D) as Supp_CEB_BED.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_EB_B BetS_D_E_C) as Supp_DEB_BEC.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_EC_C BetS_B_E_A) as Supp_BEC_CEA.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_ED_D BetS_B_E_A) as Supp_BED_DEA.

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_E_C_A Col_E_C_D neq_E_D) as nCol_E_D_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_E_D_A) as (_ & _ & nCol_A_E_D & nCol_E_A_D & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_E_A_D Col_E_A_B neq_E_B) as nCol_E_B_D.
	pose proof (by_prop_nCol_order _ _ _ nCol_E_B_D) as (nCol_B_E_D & _ & _ & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_E_A_C Col_E_A_B neq_E_B) as nCol_E_B_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_E_B_C) as (nCol_B_E_C & _ & _ & _ & _).

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_E_D) as CongA_AED_DEA.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_E_C) as CongA_BEC_CEB.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_E_D) as CongA_BED_DEB.

	pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_BED_DEB Supp_BED_DEA Supp_DEB_BEC) as CongA_DEA_BEC.
	pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_BEC_CEB Supp_BEC_CEA Supp_CEB_BED) as CongA_CEA_BED.

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_DEA_BEC CongA_BEC_CEB) as CongA_DEA_CEB.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_AED_DEA CongA_DEA_CEB) as CongA_AED_CEB.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_AED_CEB) as CongA_CEB_AED.

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_CEA_BED CongA_BED_DEB) as CongA_CEA_DEB.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_AEC_CEA CongA_CEA_DEB) as CongA_AEC_DEB.

	split.
	exact CongA_AEC_DEB.
	exact CongA_CEB_AED.
Qed.

End Euclid.
