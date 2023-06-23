Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_meet.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_collinearbetween :
	forall A B C D E F H,
	Col A E B ->
	Col C F D ->
	neq A B ->
	neq C D ->
	neq A E ->
	neq F D ->
	~ Meet A B C D ->
	BetS A H D ->
	Col E F H ->
	BetS E H F.
Proof.
	intros A B C D E F H.
	intros Col_A_E_B.
	intros Col_C_F_D.
	intros neq_A_B.
	intros neq_C_D.
	intros neq_A_E.
	intros neq_F_D.
	intros n_Meet_A_B_C_D.
	intros BetS_A_H_D.
	intros Col_E_F_H.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq D D) as eq_D_D by (reflexivity).

	pose proof (lemma_s_col_eq_A_C A B A eq_A_A) as Col_A_B_A.
	pose proof (lemma_s_col_eq_B_C C D D eq_D_D) as Col_C_D_D.

	pose proof (lemma_collinearorder _ _ _ Col_A_E_B) as (Col_E_A_B & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_E_B) as (_ & _ & _ & Col_A_B_E & _).

	pose proof (lemma_collinearorder _ _ _ Col_C_F_D) as (_ & Col_F_D_C & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_F_D) as (_ & _ & _ & Col_C_D_F & _).

	pose proof (lemma_inequalitysymmetric _ _ neq_A_E) as neq_E_A.

	pose proof (lemma_s_col_BetS_A_B_C A H D BetS_A_H_D) as Col_A_H_D.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_H_D) as BetS_D_H_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_H_D) as (_ & neq_A_H & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_H) as neq_H_A.
	pose proof (lemma_collinearorder _ _ _ Col_A_H_D) as (Col_H_A_D & _ & _ & _ & _).


	assert (~ eq H E) as n_eq_H_E.
	{
		intro eq_H_E.

		assert (Col A H B) as Col_A_H_B by (rewrite eq_H_E; exact Col_A_E_B).
		pose proof (lemma_collinearorder _ _ _ Col_A_H_B) as (Col_H_A_B & _ & _ & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_A_B Col_H_A_D neq_H_A) as Col_A_B_D.

		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_D Col_C_D_D) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}
	assert (neq_H_E := n_eq_H_E).
	pose proof (lemma_inequalitysymmetric _ _ neq_H_E) as neq_E_H.



	assert (~ eq H F) as n_eq_H_F.
	{
		intro eq_H_F.

		assert (Col A F D) as Col_A_F_D by (rewrite <- eq_H_F; exact Col_A_H_D).
		pose proof (lemma_collinearorder _ _ _ Col_A_F_D) as (_ & Col_F_D_A & _ & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_F_D_A Col_F_D_C neq_F_D) as Col_D_A_C.
		pose proof (lemma_collinearorder _ _ _ Col_D_A_C) as (_ & _ & Col_C_D_A & _ & _).

		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_A Col_C_D_A) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}
	assert (neq_H_F := n_eq_H_F).
	pose proof (lemma_inequalitysymmetric _ _ neq_H_F) as neq_F_H.

	assert (~ BetS E F H) as n_BetS_E_F_H.
	{
		intro BetS_E_F_H.

		assert (~ Col D A E) as n_Col_D_A_E.
		{
			intro Col_D_A_E.

			pose proof (lemma_collinearorder _ _ _ Col_D_A_E) as (_ & _ & _ & _ & Col_E_A_D).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_A_B Col_E_A_D neq_E_A) as Col_A_B_D.

			pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_D Col_C_D_D) as Meet_A_B_C_D.

			contradict Meet_A_B_C_D.
			exact n_Meet_A_B_C_D.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_D_A_E) as nCol_D_A_E.

		pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_E_F_H BetS_D_H_A nCol_D_A_E) as (Q & BetS_E_Q_A & BetS_D_F_Q).

		pose proof (lemma_s_col_BetS_A_B_C E Q A BetS_E_Q_A) as Col_E_Q_A.
		pose proof (lemma_s_col_BetS_A_B_C D F Q BetS_D_F_Q) as Col_D_F_Q.

		pose proof (lemma_collinearorder _ _ _ Col_E_Q_A) as (_ & _ & _ & Col_E_A_Q & _).
		pose proof (lemma_collinearorder _ _ _ Col_D_F_Q) as (Col_F_D_Q & _ & _ & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_A_Q Col_E_A_B neq_E_A) as Col_A_Q_B.
		pose proof (lemma_collinearorder _ _ _ Col_A_Q_B) as (_ & _ & _ & Col_A_B_Q & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_F_D_Q Col_F_D_C neq_F_D) as Col_D_Q_C.
		pose proof (lemma_collinearorder _ _ _ Col_D_Q_C) as (_ & _ & Col_C_D_Q & _ & _).

		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_Q Col_C_D_Q) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}


	assert (~ BetS F E H) as n_BetS_F_E_H.
	{
		intro BetS_F_E_H.

		assert (~ Col A D F) as n_Col_A_D_F.
		{
			intro Col_A_D_F.

			pose proof (lemma_collinearorder _ _ _ Col_A_D_F) as (_ & _ & _ & _ & Col_F_D_A).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_F_D_C Col_F_D_A neq_F_D) as Col_D_C_A.
			pose proof (lemma_collinearorder _ _ _ Col_D_C_A) as (Col_C_D_A & _ & _ & _ & _).

			pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_A Col_C_D_A) as Meet_A_B_C_D.

			contradict Meet_A_B_C_D.
			exact n_Meet_A_B_C_D.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_D_F) as nCol_A_D_F.

		pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_F_E_H BetS_A_H_D nCol_A_D_F) as (R & BetS_F_R_D & BetS_A_E_R).

		pose proof (lemma_s_col_BetS_A_B_C F R D BetS_F_R_D) as Col_F_R_D.
		pose proof (lemma_s_col_BetS_A_B_C A E R BetS_A_E_R) as Col_A_E_R.

		pose proof (lemma_collinearorder _ _ _ Col_F_R_D) as (_ & _ & _ & Col_F_D_R & _).
		pose proof (lemma_collinearorder _ _ _ Col_A_E_R) as (Col_E_A_R & _ & _ & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_F_D_R Col_F_D_C neq_F_D) as Col_D_R_C.
		pose proof (lemma_collinearorder _ _ _ Col_D_R_C) as (_ & _ & Col_C_D_R & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_A_R Col_E_A_B neq_E_A) as Col_A_R_B.
		pose proof (lemma_collinearorder _ _ _ Col_A_R_B) as (_ & _ & _ & Col_A_B_R & _).

		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_R Col_C_D_R) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	assert (~ eq E F) as n_eq_E_F.
	{
		intro eq_E_F.

		assert (Col A B F) as Col_A_B_F by (rewrite <- eq_E_F; exact Col_A_B_E).

		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_F Col_C_D_F) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}
	assert (neq_E_F := n_eq_E_F).

	(* assert by cases *)
	destruct Col_E_F_H as [eq_E_F | [eq_E_H | [eq_F_H | [BetS_F_E_H | [BetS_E_F_H | BetS_E_H_F]]]]].
	{
		(* case eq_E_F *)
		contradict eq_E_F.
		exact neq_E_F.
	}
	{
		(* case eq_E_H *)
		contradict eq_E_H.
		exact neq_E_H.
	}
	{
		(* case eq_F_H *)
		contradict eq_F_H.
		exact neq_F_H.
	}
	{
		(* case BetS_F_E_H *)
		contradict BetS_F_E_H.
		exact n_BetS_F_E_H.
	}
	{
		(* case BetS_E_F_H *)
		contradict BetS_E_F_H.
		exact n_BetS_E_F_H.
	}
	(* case BetS_E_H_F *)

	exact BetS_E_H_F.
Qed.

End Euclid.
