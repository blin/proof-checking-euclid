Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence_smaller.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_extension.
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
Require Import ProofCheckingEuclid.lemma_s_conga.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.proposition_05.
Require Import ProofCheckingEuclid.proposition_19.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_TogetherGreater :
        forall A B C D E F X,
        BetS A B X ->
        Cong B X C D ->
        Lt E F A X ->
        TogetherGreater A B C D E F.
Proof.
intros A B C D E F X.
intros BetS_A_B_X.
intros Cong_B_X_C_D.
intros Lt_E_F_A_X.
unfold TogetherGreater.
exists X.
split.
exact BetS_A_B_X.
split.
exact Cong_B_X_C_D.
exact Lt_E_F_A_X.
Qed.

Lemma proposition_20 :
	forall A B C,
	Triangle A B C ->
	TogetherGreater B A A C B C.
Proof.
	intros A B C.
	intros Triangle_A_B_C.

	pose proof (lemma_s_ncol_triangle _ _ _ Triangle_A_B_C) as nCol_A_B_C.
        pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.
        pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).

	pose proof (lemma_extension _ _ _ _ neq_B_A neq_C_A (* not real *)) as (D & BetS_B_A_D & Cong_A_D_C_A).
	pose proof (lemma_betweennotequal _ _ _ BetS_B_A_D) as (neq_A_D & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_D) as neq_D_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_B_A_D) as (_ & _ & neq_B_D).
	pose proof (lemma_inequalitysymmetric _ _ neq_B_D) as neq_D_B.
	
        pose proof (lemma_congruenceflip A D C A Cong_A_D_C_A) as (_ & _ & Cong_A_D_A_C).

	assert (~ Col A D C) as n_Col_A_D_C.
	{
		intro Col_A_D_C.
		pose proof (lemma_s_col_BetS_A_B_C B A D BetS_B_A_D) as Col_B_A_D.
		pose proof (lemma_collinearorder _ _ _ Col_B_A_D) as (Col_A_B_D & Col_A_D_B & Col_D_B_A & Col_B_D_A & Col_D_A_B).
		pose proof (lemma_collinearorder _ _ _ Col_A_D_C) as (Col_D_A_C & Col_D_C_A & Col_C_A_D & Col_A_C_D & Col_C_D_A).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_A_B Col_D_A_C neq_D_A) as Col_A_B_C.

                contradict Col_A_B_C.
                exact n_Col_A_B_C.
	}
        pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_D_C) as nCol_A_D_C.
        pose proof (lemma_NCdistinct _ _ _ nCol_A_D_C) as (_ & neq_D_C & _ & _ & neq_C_D & _).
        pose proof (lemma_NCorder _ _ _ nCol_A_D_C) as (nCol_D_A_C & nCol_D_C_A & nCol_C_A_D & nCol_A_C_D & nCol_C_D_A).

	pose proof (lemma_s_triangle _ _ _ nCol_A_D_C) as Triangle_A_D_C.
	pose proof (lemma_s_isosceles _ _ _ Triangle_A_D_C Cong_A_D_A_C) as isosceles_A_D_C.
	pose proof (proposition_05 _ _ _ isosceles_A_D_C) as CongA_A_D_C_A_C_D.


	pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_C_D) as CongA_A_C_D_D_C_A.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_D_C_A_C_D CongA_A_C_D_D_C_A) as CongA_A_D_C_D_C_A.
	assert (eq D D) as eq_D_D by (reflexivity).
	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).

	pose proof (lemma_s_onray_assert_ABB C D neq_C_D) as OnRay_C_D_D.
	pose proof (lemma_s_onray_assert_ABB C B neq_C_B) as OnRay_C_B_B.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_D) as BetS_D_A_B.
	epose proof (lemma_s_lta A D C D C B D A B BetS_D_A_B OnRay_C_D_D OnRay_C_B_B CongA_A_D_C_D_C_A) as LtA_A_D_C_D_C_B. (* conclude_def *)
	pose proof (lemma_s_onray_assert_bets_ABE D A B BetS_D_A_B neq_D_A) as OnRay_D_A_B.
	pose proof (lemma_s_onray_assert_ABB D C neq_D_C) as OnRay_D_C_C.
	pose proof (lemma_s_onray_assert_ABB D B neq_D_B) as OnRay_D_B_B.
	pose proof (cn_congruencereflexive D B) as Cong_D_B_D_B.
	pose proof (cn_congruencereflexive D C) as Cong_D_C_D_C.
	pose proof (cn_congruencereflexive B C) as Cong_B_C_B_C.
	epose proof (lemma_s_conga A D C B D C B C B C OnRay_D_A_B OnRay_D_C_C OnRay_D_B_B OnRay_D_C_C Cong_D_B_D_B Cong_D_C_D_C Cong_B_C_B_C nCol_A_D_C) as CongA_A_D_C_B_D_C. (* conclude_def *)
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_D_C_B_D_C) as CongA_B_D_C_A_D_C.
	pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_A_D_C_D_C_B CongA_B_D_C_A_D_C) as LtA_B_D_C_D_C_B.

	assert (~ Col B C D) as n_Col_B_C_D.
	{
		intro Col_B_C_D.
		pose proof (lemma_s_col_BetS_A_B_C B A D BetS_B_A_D) as Col_B_A_D.
		pose proof (lemma_collinearorder _ _ _ Col_B_A_D) as (Col_A_B_D & Col_A_D_B & Col_D_B_A & Col_B_D_A & Col_D_A_B).
		pose proof (lemma_collinearorder _ _ _ Col_B_C_D) as (Col_C_B_D & Col_C_D_B & Col_D_B_C & Col_B_D_C & Col_D_C_B).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_B_A Col_D_B_C neq_D_B) as Col_B_A_C.
		pose proof (lemma_collinearorder _ _ _ Col_B_A_C) as (Col_A_B_C & Col_A_C_B & Col_C_B_A & Col_B_C_A & Col_C_A_B).

                contradict Col_A_B_C.
                exact n_Col_A_B_C.
	}
        pose proof (lemma_s_n_col_ncol _ _ _ n_Col_B_C_D) as nCol_B_C_D.

        pose proof (lemma_NCorder _ _ _ nCol_B_C_D) as (nCol_C_B_D & nCol_C_D_B & nCol_D_B_C & nCol_B_D_C & nCol_D_C_B).


	pose proof (lemma_ABCequalsCBA _ _ _ nCol_C_D_B) as CongA_C_D_B_B_D_C.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_C_D) as CongA_B_C_D_D_C_B.
	pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_B_D_C_D_C_B CongA_C_D_B_B_D_C) as LtA_C_D_B_D_C_B.
	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_C_D_B_D_C_B CongA_B_C_D_D_C_B) as LtA_C_D_B_B_C_D.
	pose proof (lemma_s_triangle _ _ _ nCol_B_C_D) as Triangle_B_C_D.
	pose proof (proposition_19 _ _ _ Triangle_B_C_D LtA_C_D_B_B_C_D) as Lt_B_C_B_D.
	pose proof (lemma_s_TogetherGreater B A A C B C D BetS_B_A_D Cong_A_D_A_C Lt_B_C_B_D) as TogetherGreater_B_A_A_C_B_C. (* conclude_def *)
        exact TogetherGreater_B_A_A_C_B_C.
Qed.
End Euclid.

