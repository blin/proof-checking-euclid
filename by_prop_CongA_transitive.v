Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_prop_CongA_distinct.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_OnRay_neq_A_C.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.proposition_04.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_CongA_transitive :
	forall A B C D E F P Q R,
	CongA A B C D E F ->
	CongA D E F P Q R ->
	CongA A B C P Q R.
Proof.
	intros A B C D E F P Q R.
	intros CongA_ABC_DEF.
	intros CongA_DEF_PQR.

	assert (CongA_ABC_DEF2 := CongA_ABC_DEF).
	destruct CongA_ABC_DEF2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nCol_A_B_C).

	pose proof (by_prop_CongA_distinct _ _ _ _ _ _ CongA_ABC_DEF) as (neq_A_B & neq_B_C & _ & neq_D_E & neq_E_F & _).
	pose proof (by_prop_CongA_distinct _ _ _ _ _ _ CongA_DEF_PQR) as (_ & _ & _ & neq_P_Q & neq_Q_R & _).

	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_neq_symmetric _ _ neq_D_E) as neq_E_D.
	pose proof (by_prop_neq_symmetric _ _ neq_P_Q) as neq_Q_P.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_A) as OnRay_BA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_C) as OnRay_BC_C.

	pose proof (lemma_layoff _ _ _ _ neq_E_D neq_B_A) as (U & OnRay_ED_U & Cong_EU_BA).
	pose proof (lemma_layoff _ _ _ _ neq_E_F neq_B_C) as (V & OnRay_EF_V & Cong_EV_BC).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_EU_BA) as Cong_BA_EU.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_EV_BC) as Cong_BC_EV.

	pose proof (by_prop_OnRay_neq_A_C _ _ _ OnRay_ED_U) as neq_E_U.
	pose proof (by_prop_OnRay_neq_A_C _ _ _ OnRay_EF_V) as neq_E_V.

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_ABC_DEF OnRay_ED_U OnRay_EF_V) as CongA_ABC_UEV.
	pose proof (proposition_04 _ _ _ _ _ _ Cong_BA_EU Cong_BC_EV CongA_ABC_UEV) as (Cong_AC_UV & _ & _).

	pose proof (lemma_layoff _ _ _ _ neq_Q_P neq_E_U) as (u & OnRay_QP_u & Cong_Qu_EU).
	pose proof (lemma_layoff _ _ _ _ neq_Q_R neq_E_V) as (v & OnRay_QR_v & Cong_Qv_EV).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_Qu_EU) as Cong_EU_Qu.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_Qv_EV) as Cong_EV_Qv.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_BA_EU Cong_EU_Qu) as Cong_BA_Qu.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_BC_EV Cong_EV_Qv) as Cong_BC_Qv.

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_DEF_PQR OnRay_QP_u OnRay_QR_v) as CongA_DEF_uQv.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_DEF_uQv) as CongA_uQv_DEF.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_uQv_DEF OnRay_ED_U OnRay_EF_V) as CongA_uQv_UEV.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_uQv_UEV) as CongA_UEV_uQv.
	pose proof (proposition_04 _ _ _ _ _ _ Cong_EU_Qu Cong_EV_Qv CongA_UEV_uQv) as (Cong_UV_uv & _ & _).
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AC_UV Cong_UV_uv) as Cong_AC_uv.

	pose proof (
		by_def_CongA
		_ _ _ _ _ _
		_ _ _ _
		OnRay_BA_A
		OnRay_BC_C
		OnRay_QP_u
		OnRay_QR_v
		Cong_BA_Qu
		Cong_BC_Qv
		Cong_AC_uv
		nCol_A_B_C
	) as CongA_ABC_PQR.

	exact CongA_ABC_PQR.
Qed.

End Euclid.
