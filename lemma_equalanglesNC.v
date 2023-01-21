Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearitypreserved.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_neq_A_B.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_supporting_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_supporting_ncol_n_col.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_equalanglesNC :
	forall A B C a b c,
	CongA A B C a b c ->
	nCol a b c.
Proof.
	intros A B C a b c.
	intros CongA_ABC_abc.
	unfold CongA in CongA_ABC_abc.
	destruct CongA_ABC_abc as (
		U & V & u & v &
		OnRay_BA_U & OnRay_BC_V & OnRay_ba_u & OnRay_bc_v &
		Cong_BU_bu & Cong_BV_bv & Cong_UV_uv & nCol_A_B_C
	).
	pose proof (lemma_onray_neq_A_B _ _ _ OnRay_ba_u) as neq_b_a.
	pose proof (lemma_inequalitysymmetric _ _ neq_b_a) as neq_a_b.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BU_bu) as Cong_bu_BU.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BV_bv) as Cong_bv_BV.
	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_BA_U) as Col_B_A_U.
	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_BC_V) as Col_B_C_V.
	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_ba_u) as Col_b_a_u.
	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_bc_v) as Col_b_c_v.
	pose proof (lemma_collinearorder _ _ _ Col_b_a_u) as (Col_a_b_u & _).
	assert (~ Col a b c) as nCol_a_b_c.
	{
		intros Col_a_b_c.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_a_b_u Col_a_b_c neq_a_b) as Col_b_u_c.
		pose proof (lemma_collinearorder _ _ _ Col_b_u_c) as (_ & _ & Col_c_b_u & _).
		pose proof (lemma_collinearorder _ _ _ Col_b_c_v) as (Col_c_b_v & _).
		pose proof (lemma_onray_neq_A_B _ _ _ OnRay_bc_v) as neq_b_c.
		pose proof (lemma_inequalitysymmetric _ _ neq_b_c) as neq_c_b.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_c_b_u Col_c_b_v neq_c_b) as Col_b_u_v.
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_UV_uv) as Cong_uv_UV.
		pose proof (
			lemma_collinearitypreserved _ _ _ _ U V Col_b_u_v Cong_bu_BU Cong_bv_BV Cong_uv_UV
		) as Col_B_U_V.
		pose proof (lemma_collinearorder _ _ _ Col_B_A_U) as (_ & _ & _ & Col_B_U_A & _).
		pose proof (lemma_onray_strict _ _ _ OnRay_BA_U) as neq_B_U.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_U_V Col_B_U_A neq_B_U) as Col_U_V_A.
		pose proof (lemma_collinearorder _ _ _ Col_B_U_V) as (_ & Col_U_V_B & _).

		assert (Col V A B) as Col_V_A_B.
		assert (eq U V \/ neq U V) as [eq_U_V|neq_U_V] by (apply Classical_Prop.classic).
		{
			assert (Col_B_A_V := Col_B_A_U).
			replace U with V in Col_B_A_V.
			pose proof (lemma_collinearorder _ _ _ Col_B_A_V) as (_ & _ & _ & _ &  Col_V_A_B).
			exact Col_V_A_B.
		}
		{
			pose proof (
				lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_U_V_A Col_U_V_B neq_U_V
			) as Col_V_A_B.
			exact Col_V_A_B.
		}

		pose proof (lemma_collinearorder _ _ _ Col_V_A_B) as (_ & _ & _ & Col_V_B_A & _).
		pose proof (lemma_collinearorder _ _ _ Col_B_C_V) as (_ & _ & Col_V_B_C & _).
		pose proof (lemma_onray_strict _ _ _ OnRay_BC_V) as neq_B_V.
		pose proof (lemma_inequalitysymmetric _ _ neq_B_V) as neq_V_B.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_V_B_A Col_V_B_C neq_V_B) as Col_B_A_C.
		pose proof (lemma_collinearorder _ _ _ Col_B_A_C) as (Col_A_B_C & _).
		pose proof (lemma_supporting_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.
		contradiction n_Col_A_B_C.
	}
	apply lemma_supporting_n_col_ncol in nCol_a_b_c.
	exact nCol_a_b_c.
Qed.

End Euclid.
