Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_def_OnRay.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_OnRay_impliescollinear.
Require Import ProofCheckingEuclid.by_prop_OnRay_neq_A_C.
Require Import ProofCheckingEuclid.by_prop_OnRay_orderofpoints_any.
Require Import ProofCheckingEuclid.by_prop_OnRay_shared_initial_point.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_supplements_conga_onray_before :
	forall A B C D,
	OnRay A B C ->
	BetS D A C ->
	BetS B A D.
Proof.
	intros A B C D.
	intros OnRay_AB_C.
	intros BetS_D_A_C.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_A_C) as BetS_C_A_D.

	assert (BetS B A D) as BetS_B_A_D.
	pose proof (by_prop_OnRay_orderofpoints_any _ _ _ OnRay_AB_C) as [BetS_A_C_B|[eq_B_C|BetS_A_B_C]].
	{
		(* case BetS_A_C_B *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_B) as BetS_B_C_A.
		pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_B_C_A BetS_C_A_D) as BetS_B_A_D.
		exact BetS_B_A_D.
	}
	{
		(* case eq_B_C *)
		assert (BetS B A D) as BetS_B_A_D by (rewrite eq_B_C; exact BetS_C_A_D).
		exact BetS_B_A_D.
	}
	{
		(* case BetS_A_B_C *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_C) as BetS_C_B_A.
		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_C_B_A BetS_C_A_D) as BetS_B_A_D.
		exact BetS_B_A_D.
	}

	exact BetS_B_A_D.
Qed.

Lemma lemma_supplements_conga :
	forall A B C D F a b c d f,
	CongA A B C a b c ->
	Supp A B C D F ->
	Supp a b c d f ->
	CongA D B F d b f.
Proof.
	intros A B C D F a b c d f.
	intros CongA_ABC_abc.
	intros Supp_ABC_DBF.
	intros Supp_abc_dbf.

	destruct Supp_ABC_DBF as (OnRay_BC_D & BetS_A_B_F).
	destruct Supp_abc_dbf as (OnRay_bc_d & BetS_a_b_f).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_B_F) as (neq_B_F & neq_A_B & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_a_b_f) as (_ & neq_a_b & _).
	pose proof (by_prop_OnRay_neq_A_C _ _ _ OnRay_BC_D) as neq_B_D.

	pose proof (by_prop_neq_symmetric _ _ neq_B_D) as neq_D_B.
	pose proof (by_prop_neq_symmetric _ _ neq_B_F) as neq_F_B.

	pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_BC_D) as Col_B_C_D.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_B_F) as Col_A_B_F.

	pose proof (by_prop_Col_order _ _ _ Col_A_B_F) as (_ & _ & _ & _ & Col_F_B_A).
	pose proof (by_prop_Col_order _ _ _ Col_B_C_D) as (_ & _ & Col_D_B_C & _ & _).

	destruct CongA_ABC_abc as (U & V & u & v & OnRay_BA_U & OnRay_BC_V & OnRay_ba_u & OnRay_bc_v & Cong_BU_bu & Cong_BV_bv & Cong_UV_uv & nCol_A_B_C).

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.

	pose proof (by_prop_OnRay_shared_initial_point _ _ _ _ OnRay_BC_D OnRay_BC_V) as OnRay_BD_V.
	pose proof (by_prop_OnRay_shared_initial_point _ _ _ _ OnRay_bc_d OnRay_bc_v) as OnRay_bd_v.

	pose proof (by_prop_OnRay_neq_A_C _ _ _ OnRay_BA_U) as neq_B_U.
	pose proof (by_prop_OnRay_neq_A_C _ _ _ OnRay_ba_u) as neq_b_u.
	pose proof (by_prop_neq_symmetric _ _ neq_B_U) as neq_U_B.
	pose proof (by_prop_neq_symmetric _ _ neq_b_u) as neq_u_b.

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BU_bu) as (Cong_UB_ub & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BV_bv) as (Cong_VB_vb & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_UV_uv) as (Cong_VU_vu & _ & _).

	pose proof (lemma_extension _ _ _ _ neq_U_B neq_U_B) as (W & BetS_U_B_W & Cong_BW_UB).
	pose proof (lemma_extension _ _ _ _ neq_u_b neq_U_B) as (w & BetS_u_b_w & Cong_bw_UB).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_U_B_W) as BetS_W_B_U.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_u_b_w) as BetS_w_b_u.
	pose proof (lemma_supplements_conga_onray_before _ _ _ _ OnRay_BA_U BetS_W_B_U) as BetS_A_B_W.
	pose proof (lemma_supplements_conga_onray_before _ _ _ _ OnRay_ba_u BetS_w_b_u) as BetS_a_b_w.
	pose proof (by_def_OnRay _ _ _ _	BetS_A_B_F BetS_A_B_W) as OnRay_BF_W.
	pose proof (by_def_OnRay _ _ _ _	BetS_a_b_f BetS_a_b_w) as OnRay_bf_w.

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_bw_UB) as Cong_UB_bw.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_BW_UB Cong_UB_bw) as Cong_BW_bw.

	pose proof (
		axiom_5_line
		U B W V
		u b w v
		Cong_BW_bw
		Cong_UV_uv
		Cong_BV_bv
		BetS_U_B_W
		BetS_u_b_w
		Cong_UB_ub
	) as Cong_VW_vw.

	assert (~ Col D B F) as n_Col_D_B_F.
	{
		intros Col_D_B_F.

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_B_F Col_D_B_C neq_D_B) as Col_B_F_C.
		pose proof (by_prop_Col_order _ _ _ Col_B_F_C) as (Col_F_B_C & _ & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_F_B_A Col_F_B_C neq_F_B) as Col_B_A_C.
		pose proof (by_prop_Col_order _ _ _ Col_B_A_C) as (Col_A_B_C & _ & _ & _ & _).

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_D_B_F) as nCol_D_B_F.

	pose proof (
		by_def_CongA
		D B F d b f
		_ _ _ _
		OnRay_BD_V
		OnRay_BF_W
		OnRay_bd_v
		OnRay_bf_w
		Cong_BV_bv
		Cong_BW_bw
		Cong_VW_vw
		nCol_D_B_F
	) as Cong_DBF_dbf.
	exact Cong_DBF_dbf.
Qed.

End Euclid.
