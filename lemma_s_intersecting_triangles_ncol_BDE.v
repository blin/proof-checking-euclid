Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_intersecting_triangles_ncol_BDE :
	forall A B D E F,
	Triangle A B D ->
	Triangle B A E ->
	BetS A F D ->
	BetS B F E ->
	nCol B D E.
Proof.
	intros A B D E F.
	intros Triangle_A_B_D.
	intros Triangle_B_A_E.
	intros BetS_A_F_D.
	intros BetS_B_F_E.

	assert (nCol_A_B_D := Triangle_A_B_D).
	unfold Triangle in nCol_A_B_D.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_D) as n_Col_A_B_D.

	destruct Triangle_A_B_D as (_ & _ & neq_B_D & _ & _ & _).
	destruct Triangle_B_A_E as (_ & neq_B_E & _ & _ & _ & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_F_D) as (neq_F_D & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_B_E) as neq_E_B.

	assert (Col A F D) as Col_A_F_D by (unfold Col; one_of_disjunct BetS_A_F_D).
	assert (Col B F E) as Col_B_F_E by (unfold Col; one_of_disjunct BetS_B_F_E).
	pose proof (lemma_collinearorder _ _ _ Col_A_F_D) as (_ & Col_F_D_A & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_B_F_E) as (_ & Col_F_E_B & Col_E_B_F & _ & _).

	assert (~ eq D E) as neq_D_E.
	{
		intros eq_D_E.

		assert (Col_F_D_B := Col_F_E_B).
		replace E with D in Col_F_D_B by eq_D_E.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_F_D_A Col_F_D_B neq_F_D) as Col_D_A_B.
		pose proof (lemma_collinearorder _ _ _ Col_D_A_B) as (_ & Col_A_B_D & _ & _ & _).

		contradict Col_A_B_D.
		exact n_Col_A_B_D.
	}

	assert (~ BetS B D E) as nBetS_B_D_E.
	{
		intros BetS_B_D_E.

		assert (Col B D E) as Col_B_D_E by (unfold Col; one_of_disjunct BetS_B_D_E).
		pose proof (lemma_collinearorder _ _ _ Col_B_D_E) as (_ & _ & Col_E_B_D & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _  Col_E_B_D Col_E_B_F neq_E_B) as Col_B_D_F.
		pose proof (lemma_collinearorder _ _ _ Col_B_D_F) as (_ & _ & _ & _ & Col_F_D_B).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _  Col_F_D_A Col_F_D_B neq_F_D) as Col_D_A_B.
		pose proof (lemma_collinearorder _ _ _ Col_D_A_B) as (_ & Col_A_B_D & _).

		contradict Col_A_B_D.
		exact n_Col_A_B_D.
	}

	assert (~ BetS B E D) as nBetS_B_E_D.
	{
		intros BetS_B_E_D.

		assert (Col B E D) as Col_B_E_D by (unfold Col; one_of_disjunct BetS_B_E_D).
		pose proof (lemma_collinearorder _ _ _ Col_B_E_D) as (Col_E_B_D & _ & _ & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _  Col_E_B_D Col_E_B_F neq_E_B) as Col_B_D_F.
		pose proof (lemma_collinearorder _ _ _ Col_B_D_F) as (_ & _ & _ & _ & Col_F_D_B).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _  Col_F_D_A Col_F_D_B neq_F_D) as Col_D_A_B.
		pose proof (lemma_collinearorder _ _ _ Col_D_A_B) as (_ & Col_A_B_D & _).
		contradict Col_A_B_D.
		exact n_Col_A_B_D.
	}

	assert (~ BetS D B E) as nBetS_D_B_E.
	{
		intros BetS_D_B_E.

		assert (Col D B E) as Col_D_B_E by (unfold Col; one_of_disjunct BetS_D_B_E).
		pose proof (lemma_collinearorder _ _ _ Col_D_B_E) as (_ & _ & _ & _ & Col_E_B_D).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _  Col_E_B_D Col_E_B_F neq_E_B) as Col_B_D_F.
		pose proof (lemma_collinearorder _ _ _ Col_B_D_F) as (_ & _ & _ & _ & Col_F_D_B).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _  Col_F_D_A Col_F_D_B neq_F_D) as Col_D_A_B.
		pose proof (lemma_collinearorder _ _ _ Col_D_A_B) as (_ & Col_A_B_D & _).

		contradict Col_A_B_D.
		exact n_Col_A_B_D.
	}

	unfold nCol.
	repeat split.
	exact neq_B_D.
	exact neq_B_E.
	exact neq_D_E.
	exact nBetS_B_D_E.
	exact nBetS_B_E_D.
	exact nBetS_D_B_E.
Qed.

End Euclid.
