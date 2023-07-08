Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_oppositesidesymmetric.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_sumtwort.
Require Import ProofCheckingEuclid.lemma_s_supp.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.
Require Import ProofCheckingEuclid.lemma_supplement_symmetric.
Require Import ProofCheckingEuclid.lemma_supplements_conga.
Require Import ProofCheckingEuclid.proposition_27.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_28B :
	forall A B C D G H,
	BetS A G B ->
	BetS C H D ->
	SumTwoRT B G H G H D ->
	SS B D G H ->
	Par A B C D.
Proof.
	intros A B C D G H.
	intros BetS_A_G_B.
	intros BetS_C_H_D.
	intros SumTwoRT_B_G_H_G_H_D.
	intros SS_B_D_G_H.

	pose proof (lemma_samesidesymmetric _ _ _ _ SS_B_D_G_H) as (SS_D_B_G_H & _ & _).

	destruct SumTwoRT_B_G_H_G_H_D as (a & b & c & d & e & Supp_a_b_c_e_d & CongA_B_G_H_a_b_c & CongA_G_H_D_e_b_d).
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_B_G_H_a_b_c) as CongA_a_b_c_B_G_H.
	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_G_H_D_e_b_d) as (neq_G_H & _ & _ & _ & _ & _).
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_G_H_D_e_b_d) as CongA_e_b_d_G_H_D.
	assert (eq H H) as eq_H_H by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB G H neq_G_H) as OnRay_G_H_H.
	pose proof (lemma_s_supp _ _ _ _ _ OnRay_G_H_H BetS_A_G_B) as Supp_A_G_H_H_B.
	pose proof (lemma_supplement_symmetric _ _ _ _ _ Supp_A_G_H_H_B) as Supp_B_G_H_H_A.
	pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_a_b_c_B_G_H Supp_a_b_c_e_d Supp_B_G_H_H_A) as CongA_e_b_d_H_G_A.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_G_H_D_e_b_d CongA_e_b_d_H_G_A) as CongA_G_H_D_H_G_A.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_e_b_d_H_G_A) as nCol_H_G_A.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_H_G_A) as CongA_H_G_A_A_G_H.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_G_H_D_H_G_A CongA_H_G_A_A_G_H) as CongA_G_H_D_A_G_H.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_G_H_D_A_G_H) as CongA_A_G_H_G_H_D.
	assert (eq G G) as eq_G_G by (reflexivity).
	pose proof (lemma_s_col_eq_A_C G H G eq_G_G) as Col_G_H_G.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_H_G_A_A_G_H) as nCol_A_G_H.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_G_H) as n_Col_A_G_H.


	assert (~ Col G H A) as n_Col_G_H_A.
	{
		intro Col_G_H_A.
		pose proof (lemma_collinearorder _ _ _ Col_G_H_A) as (_ & _ & Col_A_G_H & _ & _).
		contradict Col_A_G_H.
		exact n_Col_A_G_H.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_G_H_A) as nCol_G_H_A.

	pose proof (lemma_s_os _ _ _ _ _ BetS_A_G_B Col_G_H_G nCol_G_H_A) as OS_A_G_H_B.
	pose proof (lemma_oppositesidesymmetric _ _ _ _ OS_A_G_H_B) as OS_B_G_H_A.
	pose proof (lemma_planeseparation _ _ _ _ _ SS_D_B_G_H OS_B_G_H_A) as OS_D_G_H_A.
	pose proof (lemma_oppositesidesymmetric _ _ _ _ OS_D_G_H_A) as OS_A_G_H_D.
	pose proof (proposition_27 _ _ _ _ _ _ BetS_A_G_B BetS_C_H_D CongA_A_G_H_G_H_D OS_A_G_H_D) as Par_A_B_C_D.

	exact Par_A_B_C_D.
Qed.

End Euclid.
