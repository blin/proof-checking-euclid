Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_conga :
	forall A B C a b c U V u v,
	OnRay B A U ->
	OnRay B C V ->
	OnRay b a u ->
	OnRay b c v ->
	Cong B U b u ->
	Cong B V b v ->
	Cong U V u v ->
	nCol A B C ->
	CongA A B C a b c.
Proof.
	intros A B C a b c U V u v.
	intros OnRay_BA_U.
	intros OnRay_BC_V.
	intros OnRay_ba_u.
	intros OnRay_bc_v.
	intros Cong_BU_bu.
	intros Cong_BV_bv.
	intros Cong_UV_uv.
	intros nCol_A_B_C.

	unfold CongA.
	exists U, V, u, v.
	split.
	exact OnRay_BA_U.
	split.
	exact OnRay_BC_V.
	split.
	exact OnRay_ba_u.
	split.
	exact OnRay_bc_v.
	split.
	exact Cong_BU_bu.
	split.
	exact Cong_BV_bv.
	split.
	exact Cong_UV_uv.
	exact nCol_A_B_C.
Qed.

End Euclid.
