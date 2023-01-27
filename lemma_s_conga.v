Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_conga :
	forall A B C a b c,
	Cong A B a b->
	Cong A C a c ->
	Cong B C b c ->
	nCol A B C ->
	nCol a b c ->
	CongA A B C a b c.
Proof.
	intros A B C a b c.
	intros Cong_AB_ab.
	intros Cong_AC_ac.
	intros Cong_BC_bc.
	intros nCol_A_B_C.
	intros nCol_a_b_c.

	pose proof (
		lemma_NCdistinct _ _ _ nCol_A_B_C
	) as (_ & neq_B_C & _ & neq_B_A & _).
	pose proof (lemma_s_onray_assert_ABB _ _ neq_B_A) as OnRay_BA_A.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_B_C) as OnRay_BC_C.

	pose proof (
		lemma_NCdistinct _ _ _ nCol_a_b_c
	) as (neq_a_b & neq_b_c & neq_a_c & neq_b_a & _).
	pose proof (lemma_s_onray_assert_ABB _ _ neq_b_a) as OnRay_ba_a.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_b_c) as OnRay_bc_c.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_AB_ab) as (Cong_BA_ba & _).

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
