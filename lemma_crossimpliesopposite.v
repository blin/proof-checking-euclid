Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_oppositesidesymmetric.
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
Require Import ProofCheckingEuclid.lemma_s_triangle.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_crossimpliesopposite :
	forall A B C D,
	CR A B C D ->
	nCol A C D ->
	OS A C D B /\ OS A D C B /\ OS B C D A /\ OS B D C A.
Proof.
	intros A B C D.
	intros CR_A_B_C_D.
	intros nCol_A_C_D.


	destruct CR_A_B_C_D as (M & BetS_A_M_B & BetS_C_M_D).
	pose proof (lemma_s_col_BetS_A_B_C C M D BetS_C_M_D) as Col_C_M_D.
	pose proof (lemma_collinearorder _ _ _ Col_C_M_D) as (_ & _ & _ & Col_C_D_M & _).
	pose proof (lemma_NCorder _ _ _ nCol_A_C_D) as (_ & nCol_C_D_A & _ & _ & _).
	pose proof (lemma_NCorder _ _ _ nCol_C_D_A) as (nCol_D_C_A & _ & _ & _ & _).
	pose proof (lemma_s_os _ _ _ _ _ BetS_A_M_B Col_C_D_M nCol_C_D_A) as OS_A_C_D_B.
	pose proof (lemma_collinearorder _ _ _ Col_C_D_M) as (Col_D_C_M & _ & _ & _ & _).
	pose proof (lemma_s_os _ _ _ _ _ BetS_A_M_B Col_D_C_M nCol_D_C_A) as OS_A_D_C_B.
	pose proof (lemma_oppositesidesymmetric _ _ _ _ OS_A_C_D_B) as OS_B_C_D_A.
	pose proof (lemma_oppositesidesymmetric _ _ _ _ OS_A_D_C_B) as OS_B_D_C_A.

	split.
	exact OS_A_C_D_B.
	split.
	exact OS_A_D_C_B.
	esplit.
	exact OS_B_C_D_A.
	exact OS_B_D_C_A.
Qed.

End Euclid.

