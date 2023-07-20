Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_s_conga_sss.
Require Import ProofCheckingEuclid.lemma_s_triangle_vertex_to_ray_congruent.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_04 :
	forall A B C a b c,
	Cong A B a b->
	Cong A C a c ->
	CongA B A C b a c ->
	Cong B C b c /\ CongA A B C a b c /\ CongA A C B a c b.
Proof.
	intros A B C a b c.
	intros Cong_AB_ab.
	intros Cong_AC_ac.
	intros CongA_BAC_bac.

	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_BAC_bac) as  nCol_b_a_c.

	unfold CongA in CongA_BAC_bac.
	destruct CongA_BAC_bac as (
		U & V & u & v &
		OnRay_AB_U & OnRay_AC_V &
		OnRay_ab_u & OnRay_ac_v &
		Cong_AU_au & Cong_AV_av &
		Cong_UV_uv & nCol_B_A_C
	).

	pose proof (
		lemma_s_triangle_vertex_to_ray_congruent
		_ _ _ _ _ _ _ _
		Cong_AB_ab
		Cong_AU_au
		OnRay_AB_U
		OnRay_ab_u
		Cong_AV_av
		Cong_UV_uv
	) as Cong_BV_bv.

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BV_bv) as (Cong_VB_vb & _).
	pose proof (
		lemma_s_triangle_vertex_to_ray_congruent
		_ _ _ _ _ _ _ _
		Cong_AC_ac
		Cong_AV_av
		OnRay_AC_V
		OnRay_ac_v
		Cong_AB_ab
		Cong_VB_vb
	) as Cong_CB_cb.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_CB_cb) as (Cong_BC_bc & _).

	pose proof (
		by_prop_nCol_order _ _ _ nCol_B_A_C
	) as (nCol_A_B_C & nCol_A_C_B & _).

	pose proof (
		by_prop_nCol_order _ _ _ nCol_b_a_c
	) as (nCol_a_b_c & nCol_a_c_b & _).

	pose proof (
		lemma_s_conga_sss
		A B C a b c
		Cong_AB_ab Cong_AC_ac Cong_BC_bc
		nCol_A_B_C nCol_a_b_c
	) as CongA_ABC_abc.

	pose proof (
		lemma_s_conga_sss
		A C B a c b
		Cong_AC_ac
		Cong_AB_ab
		Cong_CB_cb
		nCol_A_C_B
		nCol_a_c_b
	) as CongA_ACB_acb.

	repeat split.
	exact Cong_BC_bc.
	exact CongA_ABC_abc.
	exact CongA_ACB_acb.
Qed.

End Euclid.
