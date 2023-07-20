Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_prop_OnRay_shared_initial_point.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_CongA_helper :
	forall A B C a b c p q,
	CongA A B C a b c ->
	OnRay b a p ->
	OnRay b c q ->
	CongA A B C p b q.
Proof.
	intros A B C a b c p q.
	intros CongA_ABC_abc.
	intros OnRay_ba_p.
	intros OnRay_bc_q.

	destruct CongA_ABC_abc as (U & V & u & v & OnRay_BA_U & OnRay_BC_V & OnRay_ba_u & OnRay_bc_v & Cong_BU_bu & Cong_BV_bv & Cong_UV_uv & nCol_A_B_C).

	pose proof (by_prop_OnRay_shared_initial_point _ _ _ _ OnRay_ba_p OnRay_ba_u) as OnRay_bp_u.
	pose proof (by_prop_OnRay_shared_initial_point _ _ _ _ OnRay_bc_q OnRay_bc_v) as OnRay_bq_v.

	pose proof (
		by_def_CongA
		A B C p b q
		_ _ _ _
		OnRay_BA_U
		OnRay_BC_V
		OnRay_bp_u
		OnRay_bq_v
		Cong_BU_bu
		Cong_BV_bv
		Cong_UV_uv
		nCol_A_B_C
	) as CongA_ABC_pbq.

	exact CongA_ABC_pbq.
Qed.

End Euclid.
