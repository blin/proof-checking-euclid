Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_s_conga.


Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_equalanglessymmetric :
	forall A B C a b c,
	CongA A B C a b c ->
	CongA a b c A B C.
Proof.
	intros A B C a b c.
	intros CongA_ABC_abc.

	assert (CongA_ABC_abc2 := CongA_ABC_abc).
	destruct CongA_ABC_abc2 as (U & V & u & v & OnRay_BA_U & OnRay_BC_V & OnRay_ba_u & OnRay_bc_v & Cong_BU_bu & Cong_BV_bv & Cong_UV_uv & nCol_A_B_C).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BU_bu) as Cong_bu_BU.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BV_bv) as Cong_bv_BV.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_UV_uv) as Cong_uv_UV.

	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_ABC_abc) as nCol_a_b_c.

	pose proof (
		lemma_s_conga
		a b c A B C
		_ _ _ _
		OnRay_ba_u
		OnRay_bc_v
		OnRay_BA_U
		OnRay_BC_V
		Cong_bu_BU
		Cong_bv_BV
		Cong_uv_UV
		nCol_a_b_c
	) as CongA_abc_ABC.

	exact CongA_abc_ABC.
Qed.

End Euclid.
