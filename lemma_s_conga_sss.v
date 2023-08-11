Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_conga_sss :
	forall A B C a b c,
	Cong A B a b->
	Cong A C a c ->
	Cong B C b c ->
	nCol A B C ->
	CongA A B C a b c.
Proof.
	intros A B C a b c.
	intros Cong_AB_ab.
	intros Cong_AC_ac.
	intros Cong_BC_bc.
	intros nCol_A_B_C.

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & _ & neq_B_A & _).

	pose proof (axiom_nocollapse _ _ _ _ neq_A_B Cong_AB_ab) as neq_a_b.
	pose proof (axiom_nocollapse _ _ _ _ neq_B_C Cong_BC_bc) as neq_b_c.
	pose proof (by_prop_neq_symmetric _ _ neq_a_b) as neq_b_a.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_A) as OnRay_BA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_C) as OnRay_BC_C.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_b_a) as OnRay_ba_a.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_b_c) as OnRay_bc_c.

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_ab) as (Cong_BA_ba & _).

	unfold CongA.
	exists A, C, a, c.
	split.
	exact OnRay_BA_A.
	split.
	exact OnRay_BC_C.
	split.
	exact OnRay_ba_a.
	split.
	exact OnRay_bc_c.
	split.
	exact Cong_BA_ba.
	split.
	exact Cong_BC_bc.
	split.
	exact Cong_AC_ac.
	exact nCol_A_B_C.
Qed.

End Euclid.
