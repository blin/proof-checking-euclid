Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Euclid4.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearright.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_parallelflip.
Require Import ProofCheckingEuclid.lemma_parallelsymmetric.
Require Import ProofCheckingEuclid.lemma_right_triangle_NC.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
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
Require Import ProofCheckingEuclid.lemma_s_sumtwort.
Require Import ProofCheckingEuclid.lemma_s_supp.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.proposition_28C.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_twoperpsparallel :
	forall A B C D,
	RightTriangle A B C ->
	RightTriangle B C D ->
	SS A D B C ->
	Par A B C D.
Proof.
	intros A B C D.
	intros RightTriangle_A_B_C.
	intros RightTriangle_B_C_D.
	intros SS_A_D_B_C.

	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_A_B_C) as nCol_A_B_C.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (_ & neq_B_C & _ & _ & _ & _).

	pose proof (lemma_extension B C B C neq_B_C neq_B_C) as (E & BetS_B_C_E & Cong_C_E_B_C).

	pose proof (lemma_s_col_BetS_A_B_C B C E BetS_B_C_E) as Col_B_C_E.
	pose proof (lemma_betweennotequal _ _ _ BetS_B_C_E) as (neq_C_E & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_C_E) as neq_E_C.
	pose proof (lemma_collinearright _ _ _ _ RightTriangle_B_C_D Col_B_C_E neq_E_C) as RightTriangle_E_C_D.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_E_C_D) as RightTriangle_D_C_E.
	assert (eq D D) as eq_D_D by (reflexivity).
	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_B_C_D) as nCol_B_C_D.
	pose proof (lemma_NCdistinct _ _ _ nCol_B_C_D) as (_ & neq_C_D & _ & _ & _ & _).
	pose proof (lemma_s_onray_assert_ABB C D neq_C_D) as OnRay_C_D_D.
	pose proof (lemma_s_supp _ _ _ _ _ OnRay_C_D_D BetS_B_C_E) as Supp_B_C_D_D_E.
	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_A_B_C RightTriangle_B_C_D) as CongA_A_B_C_B_C_D.
	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_B_C_D RightTriangle_D_C_E) as CongA_B_C_D_D_C_E.
	pose proof (lemma_s_sumtwort _ _ _ _ _ _ _ _ _ _ _ Supp_B_C_D_D_E CongA_A_B_C_B_C_D CongA_B_C_D_D_C_E) as SumTwoRT_A_B_C_B_C_D.
	pose proof (proposition_28C _ _ _ _ SumTwoRT_A_B_C_B_C_D SS_A_D_B_C) as Par_B_A_C_D.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_B_A_C_D) as Par_C_D_B_A.
	pose proof (lemma_parallelflip _ _ _ _ Par_C_D_B_A) as (_ & Par_C_D_A_B & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_C_D_A_B) as Par_A_B_C_D.

	exact Par_A_B_C_D.
Qed.

End Euclid.

