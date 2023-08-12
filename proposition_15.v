Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_Supp.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
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

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_E_D) as BetS_D_E_C.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_E_D) as (neq_E_D & _ & _).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_E_D) as Col_C_E_D.
	pose proof (by_prop_Col_order _ _ _ Col_C_E_D) as (Col_E_C_D & _ & _ & _ & _).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_E_C) as (_ & neq_E_C & _ & neq_E_A & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_E_C) as (_ & nCol_E_C_A & _ & _ & _).
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_E_C) as CongA_AEC_CEA.

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_E_C_A Col_E_C_D neq_E_D) as nCol_E_D_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_E_D_A) as (_ & _ & nCol_A_E_D & _ & _).

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_E_D) as CongA_AED_DEA.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_E_A) as OnRay_EA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_E_C) as OnRay_EC_C.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_E_D) as OnRay_ED_D.

	pose proof (by_def_Supp _ _ _ _ _ OnRay_EC_C BetS_A_E_B) as Supp_AEC_CEB.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_EA_A BetS_C_E_D) as Supp_CEA_AED.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_ED_D BetS_A_E_B) as Supp_AED_DEB.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_EA_A BetS_D_E_C) as Supp_DEA_AEC.

	pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_AEC_CEA Supp_AEC_CEB Supp_CEA_AED) as CongA_CEB_AED.
	pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_AED_DEA Supp_AED_DEB Supp_DEA_AEC) as CongA_DEB_AEC.

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_DEB_AEC) as CongA_AEC_DEB.

	split.
	exact CongA_AEC_DEB.
	exact CongA_CEB_AED.
Qed.

End Euclid.
