Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence2.
Require Import ProofCheckingEuclid.lemma_angletrichotomy.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_s_lta.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.proposition_03.
Require Import ProofCheckingEuclid.proposition_04.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.


Lemma proposition_06a : 
	forall A B C,
	Triangle A B C ->
	CongA A B C A C B ->
	~ Lt A C A B.
Proof.
	intros A B C.
	intros Triangle_A_B_C.
	intros CongA_A_B_C_A_C_B.

	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_A_B_C_A_C_B) as (neq_A_B & neq_B_C & neq_A_C & _ & neq_C_B & _).

	pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.
	pose proof (lemma_inequalitysymmetric _ _ neq_A_C) as neq_C_A.

	assert (~ Lt A C A B) as n_Lt_A_C_A_B.
	{
		intros Lt_A_C_A_B.

		pose proof (cn_congruencereverse B A) as Cong_B_A_A_B.
		pose proof (proposition_03 _ _ A C B A Lt_A_C_A_B Cong_B_A_A_B) as (D & BetS_B_D_A & Cong_B_D_A_C).
		pose proof (lemma_congruenceflip _ _ _ _ Cong_B_D_A_C) as (_ & Cong_D_B_A_C & _ ).
		pose proof (cn_congruencereflexive B C) as Cong_B_C_B_C.
		pose proof (lemma_s_onray_assert_bets_AEB _ _ _ BetS_B_D_A neq_B_A) as OnRay_B_A_D.
		assert (eq C C) as eq_C_C by (reflexivity).
		pose proof (lemma_s_onray_assert_ABB _ _ neq_B_C) as OnRay_B_C_C.
		assert (nCol A B C) as nCol_A_B_C by (unfold Triangle in Triangle_A_B_C; exact Triangle_A_B_C).
		pose proof (lemma_equalanglesreflexive _ _ _ nCol_A_B_C) as CongA_A_B_C_A_B_C.
		pose proof (lemma_equalangleshelper _ _ _ _ _ _ D C CongA_A_B_C_A_B_C OnRay_B_A_D OnRay_B_C_C) as CongA_A_B_C_D_B_C.
		pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_B_C_D_B_C) as CongA_D_B_C_A_B_C.
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ A C B CongA_D_B_C_A_B_C CongA_A_B_C_A_C_B) as CongA_D_B_C_A_C_B.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_D_B_A_C) as (Cong_B_D_C_A & _ & _).
		pose proof (cn_congruencereverse B C) as Cong_B_C_C_B.
		pose proof (proposition_04 B D C C A B Cong_B_D_C_A Cong_B_C_C_B CongA_D_B_C_A_C_B) as (Cong_D_C_A_B & CongA_B_D_C_C_A_B & CongA_B_C_D_C_B_A).

		pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).

		pose proof (lemma_ABCequalsCBA _ _ _ nCol_C_B_A) as CongA_C_B_A_A_B_C.
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ A B C CongA_B_C_D_C_B_A CongA_C_B_A_A_B_C) as CongA_B_C_D_A_B_C.
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ A C B CongA_B_C_D_A_B_C CongA_A_B_C_A_C_B) as CongA_B_C_D_A_C_B.

		pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_C_B) as CongA_A_C_B_B_C_A.
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ B C A CongA_B_C_D_A_C_B CongA_A_C_B_B_C_A) as CongA_B_C_D_B_C_A.

		pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_B_C_D_B_C_A) as CongA_B_C_A_B_C_D.
		assert (eq B B) as eq_B_B by (reflexivity).
		assert (eq A A) as eq_A_A by (reflexivity).
		pose proof (lemma_s_onray_assert_ABB _ _ neq_C_B) as OnRay_C_B_B.
		pose proof (lemma_s_onray_assert_ABB _ _ neq_C_A) as OnRay_C_A_A.

		assert (Col B D A) as Col_B_D_A by (unfold Col; one_of_disjunct BetS_B_D_A).
		pose proof (lemma_collinearorder _ _ _ Col_B_D_A) as (Col_D_B_A & _ & _ & _ & _).

		assert (~ Col B C D) as n_Col_B_C_D.
		{
			intros Col_B_C_D.

			pose proof (lemma_collinearorder _ _ _ Col_B_C_D) as (_ & _ & Col_D_B_C & _ & _).

			pose proof (lemma_betweennotequal _ _ _ BetS_B_D_A) as (_ & neq_B_D & _).
			pose proof (lemma_inequalitysymmetric _ _ neq_B_D) as neq_D_B.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_B_A Col_D_B_C neq_D_B) as Col_B_A_C.
			pose proof (lemma_collinearorder _ _ _ Col_B_A_C) as (Col_A_B_C & _ & _ & _ & _).

			pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.

			contradict Col_A_B_C.
			exact n_Col_A_B_C.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_B_C_D) as nCol_B_C_D.
		pose proof (lemma_equalanglesreflexive _ _ _ nCol_B_C_D) as CongA_B_C_D_B_C_D.

		pose proof (lemma_s_lta _ _ _ _ _ _ B D A BetS_B_D_A OnRay_C_B_B OnRay_C_A_A CongA_B_C_D_B_C_D) as LtA_B_C_D_B_C_A.
		pose proof (lemma_angleorderrespectscongruence2 _ _ _ _ _ _ B C A LtA_B_C_D_B_C_A CongA_B_C_A_B_C_D) as LtA_B_C_A_B_C_A.
		pose proof (lemma_angletrichotomy _ _ _ _ _ _ LtA_B_C_A_B_C_A) as n_LtA_B_C_A_B_C_A.

		contradict LtA_B_C_A_B_C_A.
		exact n_LtA_B_C_A_B_C_A.
	}

	exact n_Lt_A_C_A_B.

Qed.

End Euclid.
