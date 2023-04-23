Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence_smaller.
Require Import ProofCheckingEuclid.lemma_angleordertransitive.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_lta.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.proposition_03.
Require Import ProofCheckingEuclid.proposition_05.
Require Import ProofCheckingEuclid.proposition_16.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_18 :
	forall A B C,
	Triangle A B C ->
	Lt A B A C ->
	LtA B C A A B C.
Proof.
	intros A B C.
	intros Triangle_A_B_C.
	intros Lt_A_B_A_C.

	pose proof (lemma_s_ncol_triangle A B C Triangle_A_B_C) as nCol_A_B_C.
	pose proof (lemma_s_ncol_n_col A B C nCol_A_B_C) as n_Col_A_B_C.

	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).

	pose proof (cn_congruencereflexive A C) as Cong_A_C_A_C.
	pose proof (proposition_03 A C A B A C Lt_A_B_A_C Cong_A_C_A_C) as (D & BetS_A_D_C & Cong_A_D_A_B).

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_D_C) as Col_A_D_C.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_D_C) as (neq_D_C & neq_A_D & _).
	pose proof (lemma_inequalitysymmetric A D neq_A_D) as neq_D_A.
	pose proof (lemma_inequalitysymmetric _ _ neq_D_C) as neq_C_D.
	pose proof (lemma_collinearorder _ _ _ Col_A_D_C) as (Col_D_A_C & Col_D_C_A & Col_C_A_D & Col_A_C_D & Col_C_D_A).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_C_A_B Col_C_A_D neq_C_D) as nCol_C_D_B.
	pose proof (lemma_NCdistinct _ _ _ nCol_C_D_B) as (_ & neq_D_B & _ & _ & neq_B_D & _).
	pose proof (lemma_NCorder _ _ _ nCol_C_D_B) as (nCol_D_C_B & nCol_D_B_C & nCol_B_C_D & nCol_C_B_D & nCol_B_D_C).

	pose proof (lemma_s_triangle B C D nCol_B_C_D) as Triangle_B_C_D.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_C) as BetS_C_D_A.
	
	pose proof (proposition_16 B C D A Triangle_B_C_D BetS_C_D_A) as (_ & LtA_D_C_B_B_D_A).
	
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_C_B Col_A_C_D neq_A_D) as nCol_A_D_B.
	pose proof (lemma_NCorder _ _ _ nCol_A_D_B) as (nCol_D_A_B & nCol_D_B_A & nCol_B_A_D & nCol_A_B_D & nCol_B_D_A).

	pose proof (lemma_s_triangle A D B nCol_A_D_B) as Triangle_A_D_B.
	pose proof (lemma_s_isosceles _ _ _ Triangle_A_D_B Cong_A_D_A_B) as isosceles_A_D_B.
	pose proof (proposition_05 _ _ _ isosceles_A_D_B) as CongA_A_D_B_A_B_D.
	pose proof (lemma_s_onray_assert_bets_AEB C A D BetS_C_D_A neq_C_A) as OnRay_C_A_D.
	assert (eq B B) as eq_B_B by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB C B neq_C_B) as OnRay_C_B_B.

	pose proof (lemma_equalanglesreflexive A C B nCol_A_C_B) as CongA_A_C_B_A_C_B.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_A_C_B_A_C_B OnRay_C_A_D OnRay_C_B_B) as CongA_A_C_B_D_C_B.
	pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_D_C_B_B_D_A CongA_A_C_B_D_C_B) as LtA_A_C_B_B_D_A.
	pose proof (lemma_ABCequalsCBA A D B nCol_A_D_B) as CongA_A_D_B_B_D_A.
	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_A_C_B_B_D_A CongA_A_D_B_B_D_A) as LtA_A_C_B_A_D_B.
	pose proof (lemma_equalanglessymmetric A D B A B D CongA_A_D_B_A_B_D) as CongA_A_B_D_A_D_B.
	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_A_C_B_A_D_B CongA_A_B_D_A_D_B) as LtA_A_C_B_A_B_D.

	pose proof (lemma_ABCequalsCBA B C A nCol_B_C_A) as CongA_B_C_A_A_C_B.
	pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_A_C_B_A_B_D CongA_B_C_A_A_C_B) as LtA_B_C_A_A_B_D.
	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB B C neq_B_C) as OnRay_B_C_C.
	pose proof (lemma_s_onray_assert_ABB B A neq_B_A) as OnRay_B_A_A.

	pose proof (lemma_equalanglesreflexive A B D nCol_A_B_D) as CongA_A_B_D_A_B_D.
	pose proof (lemma_s_lta _ _ _ _ _ _ _ _ _ BetS_A_D_C OnRay_B_A_A OnRay_B_C_C CongA_A_B_D_A_B_D) as LtA_A_B_D_A_B_C.
	pose proof (lemma_angleordertransitive _ _ _ _ _ _ _ _ _ LtA_B_C_A_A_B_D LtA_A_B_D_A_B_C) as LtA_B_C_A_A_B_C.

	exact LtA_B_C_A_A_B_C.
Qed.

End Euclid.
