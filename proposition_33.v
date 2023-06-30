Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_meet.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_par.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_27B.
Require Import ProofCheckingEuclid.proposition_29B.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_33 :
	forall A B C D M,
	Par A B C D ->
	Cong A B C D ->
	BetS A M D ->
	BetS B M C ->
	Par A C B D /\ Cong A C B D.
Proof.
	intros A B C D M.
	intros Par_A_B_C_D.
	intros Cong_A_B_C_D.
	intros BetS_A_M_D.
	intros BetS_B_M_C.


	assert (Par_A_B_C_D_2 := Par_A_B_C_D).
	destruct Par_A_B_C_D_2 as (a & b & c & d & m & neq_A_B & neq_C_D & Col_A_B_a & Col_A_B_b & neq_a_b & Col_C_D_c & Col_C_D_d & neq_c_d & n_Meet_A_B_C_D & BetS_a_m_d & BetS_c_m_b).
	pose proof (lemma_s_col_BetS_A_B_C B M C BetS_B_M_C) as Col_B_M_C.
	pose proof (lemma_collinearorder _ _ _ Col_B_M_C) as (_ & _ & _ & Col_B_C_M & _).

	assert (~ Col B C A) as n_Col_B_C_A.
	{
		intro Col_B_C_A.
		pose proof (lemma_collinearorder _ _ _ Col_B_C_A) as (_ & _ & Col_A_B_C & _ & _).
		assert (eq C C) as eq_C_C by (reflexivity).
		pose proof (lemma_s_col_eq_A_C C D C eq_C_C) as Col_C_D_C.
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_C Col_C_D_C) as Meet_A_B_C_D.
		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_B_C_A) as nCol_B_C_A.

	pose proof (lemma_s_os _ _ _ _ _ BetS_A_M_D Col_B_C_M nCol_B_C_A) as OS_A_B_C_D.
	pose proof (proposition_29B _ _ _ _ Par_A_B_C_D OS_A_B_C_D) as CongA_A_B_C_B_C_D.

	assert (~ Col B C D) as n_Col_B_C_D.
	{
		intro Col_B_C_D.
		pose proof (lemma_collinearorder _ _ _ Col_B_C_D) as (_ & Col_C_D_B & _ & _ & _).
		assert (eq B B) as eq_B_B by (reflexivity).
		pose proof (lemma_s_col_eq_B_C A B B eq_B_B) as Col_A_B_B.
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_B Col_C_D_B) as Meet_A_B_C_D.
		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_B_C_D) as nCol_B_C_D.

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_C_D) as CongA_B_C_D_D_C_B.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_B_C_B_C_D CongA_B_C_D_D_C_B) as CongA_A_B_C_D_C_B.
	pose proof (cn_congruencereflexive B C) as Cong_B_C_B_C.
	pose proof (lemma_NCorder _ _ _ nCol_B_C_A) as (_ & _ & nCol_A_B_C & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_A_B_C_D) as (_ & Cong_B_A_C_D & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_B_C_B_C) as (_ & _ & Cong_B_C_C_B).
	pose proof (proposition_04 _ _ _ _ _ _ Cong_B_A_C_D Cong_B_C_C_B CongA_A_B_C_D_C_B) as (Cong_A_C_D_B & CongA_B_A_C_C_D_B & CongA_B_C_A_C_B_D).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (_ & _ & _ & nCol_A_C_B & _).
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_C_B) as CongA_A_C_B_B_C_A.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_C_B_B_C_A CongA_B_C_A_C_B_D) as CongA_A_C_B_C_B_D.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_A_C_D_B) as (_ & _ & Cong_A_C_B_D).
	pose proof (lemma_collinearorder _ _ _ Col_B_C_M) as (Col_C_B_M & _ & _ & _ & _).
	pose proof (lemma_NCorder _ _ _ nCol_B_C_A) as (nCol_C_B_A & _ & _ & _ & _).
	pose proof (lemma_s_os _ _ _ _ _ BetS_A_M_D Col_C_B_M nCol_C_B_A) as OS_A_C_B_D.
	pose proof (proposition_27B _ _ _ _ CongA_A_C_B_C_B_D OS_A_C_B_D) as Par_A_C_B_D.

	split.
	exact Par_A_C_B_D.
	exact Cong_A_C_B_D.
Qed.

End Euclid.

