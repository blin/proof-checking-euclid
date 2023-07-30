Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_intersecting_triangles_ncol_ADE :
	forall A B D E F,
	Triangle A B D ->
	Triangle B A E ->
	BetS A F D ->
	BetS B F E ->
	nCol A D E.
Proof.
	intros A B D E F.
	intros Triangle_ABD.
	intros Triangle_BAE.
	intros BetS_A_F_D.
	intros BetS_B_F_E.

	assert (nCol_A_B_D := Triangle_ABD).
	unfold Triangle in nCol_A_B_D.

	assert (nCol_B_A_E := Triangle_BAE).
	unfold Triangle in nCol_B_A_E.

	destruct Triangle_ABD as (_ & neq_A_D & _ & _ & _ & _).
	destruct Triangle_BAE as (_ & _ & neq_A_E & _ & _ & _).
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_D) as n_Col_A_B_D.
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_B_A_E) as n_Col_B_A_E.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_F_D) as (neq_F_D & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_F_E) as (neq_F_E & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_A_D) as neq_D_A.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_F_D) as Col_A_F_D.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_F_E) as Col_B_F_E.
	pose proof (by_prop_Col_order _ _ _ Col_A_F_D) as (_ & Col_F_D_A & Col_D_A_F & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_B_F_E) as (_ & Col_F_E_B & _ & _ & _).

	assert (~ eq D E) as neq_D_E.
	{
		intros eq_D_E.

		assert (Col F D B) as Col_F_D_B by (rewrite eq_D_E; exact Col_F_E_B).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_F_D_A Col_F_D_B neq_F_D) as Col_D_A_B.
		pose proof (by_prop_Col_order _ _ _ Col_D_A_B) as (_ & Col_A_B_D & _ & _ & _).

		contradict Col_A_B_D.
		exact n_Col_A_B_D.
	}

	assert (~ BetS A D E) as nBetS_A_D_E.
	{
		intros BetS_A_D_E.

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_D_E) as Col_A_D_E.
		pose proof (by_prop_Col_order _ _ _ Col_A_D_E) as (Col_D_A_E & _ & _ & _ & _).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_A_E Col_D_A_F neq_D_A) as Col_A_E_F.
		pose proof (by_prop_Col_order _ _ _ Col_A_E_F) as (_ & _ & _ & _ & Col_F_E_A).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_F_E_A Col_F_E_B neq_F_E) as Col_E_A_B.
		pose proof (by_prop_Col_order _ _ _ Col_E_A_B) as (_ & _ & _ & _ & Col_B_A_E).

		contradict Col_B_A_E.
		exact n_Col_B_A_E.
	}

	assert (~ BetS A E D) as nBetS_A_E_D.
	{
		intros BetS_A_E_D.
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_E_D) as Col_A_E_D.

		pose proof (by_prop_Col_order _ _ _ Col_A_E_D) as (_ & _ & Col_D_A_E & _ & _).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_A_E Col_D_A_F neq_D_A) as Col_A_E_F.
		pose proof (by_prop_Col_order _ _ _ Col_A_E_F) as (_ & _ & _ & _ & Col_F_E_A).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_F_E_A Col_F_E_B neq_F_E) as Col_E_A_B.
		pose proof (by_prop_Col_order _ _ _ Col_E_A_B) as (_ & _ & _ & _ & Col_B_A_E).

		contradict Col_B_A_E.
		exact n_Col_B_A_E.
	}

	assert (~ BetS D A E) as nBetS_D_A_E.
	{
		intros BetS_D_A_E.

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_D_A_E) as Col_D_A_E.

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_A_E Col_D_A_F neq_D_A) as Col_A_E_F.
		pose proof (by_prop_Col_order _ _ _ Col_A_E_F) as (_ & _ & _ & _ & Col_F_E_A).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_F_E_A Col_F_E_B neq_F_E) as Col_E_A_B.
		pose proof (by_prop_Col_order _ _ _ Col_E_A_B) as (_ & _ & _ & _ & Col_B_A_E).

		contradict Col_B_A_E.
		exact n_Col_B_A_E.
	}

	unfold nCol.
	repeat split.
	exact neq_A_D.
	exact neq_A_E.
	exact neq_D_E.
	exact nBetS_A_D_E.
	exact nBetS_A_E_D.
	exact nBetS_D_A_E.
Qed.

End Euclid.
