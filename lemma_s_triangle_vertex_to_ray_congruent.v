Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_differenceofparts.
Require Import ProofCheckingEuclid.lemma_interior5.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_neq_A_B.
Require Import ProofCheckingEuclid.lemma_onray_orderofpoints_any.
Require Import ProofCheckingEuclid.lemma_s_onray_congruence_betweenness.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_triangle_vertex_to_ray_congruent_BetS_A_U_B :
	forall A B U a b u V v,
	Cong A B a b->
	Cong A U a u ->
	BetS A U B ->
	OnRay a b u ->
	Cong A V a v ->
	Cong U V u v ->
	Cong B V b v.
Proof.
	intros A B U a b u V v.
	intros Cong_AB_ab.
	intros Cong_AU_au.
	intros BetS_A_U_B.
	intros OnRay_ab_u.
	intros Cong_AV_av.
	intros Cong_UV_uv.

	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_ab_u) as OnRay_au_b.
	pose proof (
		lemma_s_onray_congruence_betweenness
		_ _ _ _ _ _
		Cong_AU_au Cong_AB_ab
		OnRay_au_b BetS_A_U_B
	) as BetS_a_u_b.

	pose proof (
		lemma_differenceofparts _ _ _ _ _ _ Cong_AU_au Cong_AB_ab BetS_A_U_B BetS_a_u_b
	) as Cong_UB_ub.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AV_av) as (Cong_VA_va & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_UV_uv) as (Cong_VU_vu & _).

	(* △AUV and △auv are SSS congruent. *)
	(* △VUB and △vub are SAS congruent. *)
	(* ∠AUV is supplement to ∠VUB and ∠auv is supplement to ∠vub . *)
	(* △VUB ≅ △VUB implies that BV ≅ bv . *)
	pose proof (
		axiom_5_line
		A U B V
		a u b v

		Cong_UB_ub
		Cong_AV_av
		Cong_UV_uv
		BetS_A_U_B
		BetS_a_u_b
		Cong_AU_au
	) as Cong_VB_vb.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_VB_vb) as (Cong_BV_bv & _).

	exact Cong_BV_bv.
Qed.

Lemma lemma_s_triangle_vertex_to_ray_congruent_eq_B_U :
	forall A B U a b u V v,
	Cong A B a b->
	Cong A U a u ->
	eq B U ->
	OnRay a b u ->
	Cong A V a v ->
	Cong U V u v ->
	Cong B V b v.
Proof.
	intros A B U a b u V v.
	intros Cong_AB_ab.
	intros Cong_AU_au.
	intros eq_B_U.
	intros OnRay_ab_u.
	intros Cong_AV_av.
	intros Cong_UV_uv.

	assert (Cong A B a u) as Cong_AB_au by (rewrite eq_B_U; exact Cong_AU_au).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AB_ab) as Cong_ab_AB.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_ab_AB Cong_AB_au) as Cong_ab_au.
	pose proof (lemma_onray_neq_A_B _ _ _ OnRay_ab_u) as neq_a_b.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_a_b) as OnRay_ab_b.
	pose proof (lemma_layoffunique _ _ _ _ OnRay_ab_b OnRay_ab_u Cong_ab_au) as eq_b_u.

	assert (Cong B V u v) as Cong_BV_uv by (rewrite eq_B_U; exact Cong_UV_uv).
	assert (Cong B V b v) as Cong_BV_bv by (rewrite eq_b_u; exact Cong_BV_uv).

	exact Cong_BV_bv.
Qed.

Lemma lemma_s_triangle_vertex_to_ray_congruent_BetS_A_B_U :
	forall A B U a b u V v,
	Cong A B a b->
	Cong A U a u ->
	BetS A B U ->
	OnRay a b u ->
	Cong A V a v ->
	Cong U V u v ->
	Cong B V b v.
Proof.
	intros A B U a b u V v.
	intros Cong_AB_ab.
	intros Cong_AU_au.
	intros BetS_A_B_U.
	intros OnRay_ab_u.
	intros Cong_AV_av.
	intros Cong_UV_uv.

	pose proof (
		lemma_s_onray_congruence_betweenness
		_ _ _ _ _ _
		Cong_AB_ab Cong_AU_au
		OnRay_ab_u BetS_A_B_U
	) as BetS_a_b_u.

	pose proof (
		lemma_differenceofparts _ _ _ _ _ _ Cong_AB_ab Cong_AU_au BetS_A_B_U BetS_a_b_u
	) as Cong_BU_bu.

	pose proof (
		lemma_interior5
		A B U V
		a b u v

		BetS_A_B_U
		BetS_a_b_u

		Cong_AB_ab
		Cong_BU_bu
		Cong_AV_av
		Cong_UV_uv
	) as Cong_BV_bv.
	exact Cong_BV_bv.
Qed.

Lemma lemma_s_triangle_vertex_to_ray_congruent :
	forall A B U a b u V v,
	Cong A B a b->
	Cong A U a u ->
	OnRay A B U ->
	OnRay a b u ->
	Cong A V a v ->
	Cong U V u v ->
	Cong B V b v.
Proof.
	intros A B U a b u V v.
	intros Cong_AB_ab.
	intros Cong_AU_au.
	intros OnRay_AB_U.
	intros OnRay_ab_u.
	intros Cong_AV_av.
	intros Cong_UV_uv.

	pose proof (
		lemma_onray_orderofpoints_any _ _ _ OnRay_AB_U
	) as [BetS_A_U_B | [eq_B_U | BetS_A_B_U]].
	{
		(* case BetS_A_U_B *)
		pose proof (
			lemma_s_triangle_vertex_to_ray_congruent_BetS_A_U_B
			_ _ _ _ _ _ _ _
			Cong_AB_ab
			Cong_AU_au
			BetS_A_U_B
			OnRay_ab_u

			Cong_AV_av
			Cong_UV_uv
		) as Cong_BV_bv.
		exact Cong_BV_bv.
	}
	{
		(* case eq_B_U *)
		pose proof (
			lemma_s_triangle_vertex_to_ray_congruent_eq_B_U
			_ _ _ _ _ _ _ _
			Cong_AB_ab
			Cong_AU_au
			eq_B_U
			OnRay_ab_u
			Cong_AV_av
			Cong_UV_uv
		) as Cong_BV_bv.
		exact Cong_BV_bv.
	}
	{
		(* case BetS_A_B_U *)
		pose proof (
			lemma_s_triangle_vertex_to_ray_congruent_BetS_A_B_U
			_ _ _ _ _ _ _ _
			Cong_AB_ab
			Cong_AU_au
			BetS_A_B_U
			OnRay_ab_u
			Cong_AV_av
			Cong_UV_uv
		) as Cong_BV_bv.
		exact Cong_BV_bv.
	}
Qed.

End Euclid.
