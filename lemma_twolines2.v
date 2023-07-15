Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Coq.Logic.Classical_Prop.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

(* TODO: rename to lemma_line_intersection_unique_col *)
Lemma lemma_twolines2 :
	forall A B C D P Q,
	neq A B ->
	neq C D ->
	Col P A B ->
	Col P C D ->
	Col Q A B ->
	Col Q C D ->
	~ (Col A C D /\ Col B C D) ->
	eq P Q.
Proof.
	intros A B C D P Q.
	intros neq_A_B.
	intros neq_C_D.
	intros Col_P_A_B.
	intros Col_P_C_D.
	intros Col_Q_A_B.
	intros Col_Q_C_D.
	intros n_Col_A_C_D_and_Col_B_C_D.

	pose proof (lemma_collinearorder _ _ _ Col_P_A_B) as (Col_A_P_B & Col_A_B_P & Col_B_P_A & Col_P_B_A & Col_B_A_P).
	pose proof (lemma_collinearorder _ _ _ Col_P_C_D) as (Col_C_P_D & Col_C_D_P & Col_D_P_C & Col_P_D_C & Col_D_C_P).
	pose proof (lemma_collinearorder _ _ _ Col_Q_A_B) as (Col_A_Q_B & Col_A_B_Q & Col_B_Q_A & Col_Q_B_A & Col_B_A_Q).
	pose proof (lemma_collinearorder _ _ _ Col_Q_C_D) as (Col_C_Q_D & Col_C_D_Q & Col_D_Q_C & Col_Q_D_C & Col_D_C_Q).

	pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.
	pose proof (lemma_inequalitysymmetric _ _ neq_C_D) as neq_D_C.

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_Q Col_B_A_P neq_B_A) as Col_A_Q_P.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_P Col_A_B_Q neq_A_B) as Col_B_P_Q.
	pose proof (lemma_collinearorder _ _ _ Col_A_Q_P) as (Col_Q_A_P & Col_Q_P_A & Col_P_A_Q & Col_A_P_Q & Col_P_Q_A).
	pose proof (lemma_collinearorder _ _ _ Col_B_P_Q) as (Col_P_B_Q & Col_P_Q_B & Col_Q_B_P & Col_B_Q_P & Col_Q_P_B).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_C_P Col_D_C_Q neq_D_C) as Col_C_P_Q.
	pose proof (lemma_collinearorder _ _ _ Col_C_P_Q) as (Col_P_C_Q & Col_P_Q_C & Col_Q_C_P & Col_C_Q_P & Col_Q_P_C).

	assert (~ neq P Q) as eq_P_Q.
	{
		intros neq_P_Q.

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_P_Q_C Col_P_Q_A neq_P_Q) as Col_Q_C_A.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_P_Q_C Col_P_Q_B neq_P_Q) as Col_Q_C_B.
		pose proof (lemma_collinearorder _ _ _ Col_Q_C_A) as (Col_C_Q_A & Col_C_A_Q & Col_A_Q_C & Col_Q_A_C & Col_A_C_Q).
		pose proof (lemma_collinearorder _ _ _ Col_Q_C_B) as (Col_C_Q_B & Col_C_B_Q & Col_B_Q_C & Col_Q_B_C & Col_B_C_Q).

		assert (eq Q C \/ neq Q C) as [eq_Q_C|neq_Q_C] by (apply Classical_Prop.classic).
		{
			(* case eq_Q_C *)
			pose proof (lemma_equalitysymmetric _ _ eq_Q_C) as eq_C_Q.
			assert (Col C P B) as Col_C_P_B by (rewrite eq_C_Q; exact Col_Q_P_B).
			assert (Col C P A) as Col_C_P_A by (rewrite eq_C_Q; exact Col_Q_P_A).
			pose proof (lemma_collinearorder _ _ _ Col_C_P_B) as (Col_P_C_B & Col_P_B_C & Col_B_C_P & Col_C_B_P & Col_B_P_C).
			pose proof (lemma_collinearorder _ _ _ Col_C_P_A) as (Col_P_C_A & Col_P_A_C & Col_A_C_P & Col_C_A_P & Col_A_P_C).

			assert (~ eq P C) as neq_P_C by (rewrite eq_C_Q; exact neq_P_Q).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_P_C_D Col_P_C_A neq_P_C) as Col_C_D_A.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_P_C_D Col_P_C_B neq_P_C) as Col_C_D_B.
			pose proof (lemma_collinearorder _ _ _ Col_C_D_A) as (Col_D_C_A & Col_D_A_C & Col_A_C_D & Col_C_A_D & Col_A_D_C).
			pose proof (lemma_collinearorder _ _ _ Col_C_D_B) as (Col_D_C_B & Col_D_B_C & Col_B_C_D & Col_C_B_D & Col_B_D_C).

			contradict n_Col_A_C_D_and_Col_B_C_D.
			split.
			exact Col_A_C_D.
			exact Col_B_C_D.
		}
		{
			(* case neq_Q_C *)
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_C_B Col_Q_C_D neq_Q_C) as Col_C_B_D.
			pose proof (lemma_collinearorder _ _ _ Col_C_B_D) as (Col_B_C_D & Col_B_D_C & Col_D_C_B & Col_C_D_B & Col_D_B_C).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_C_A Col_Q_C_D neq_Q_C) as Col_C_A_D.
			pose proof (lemma_collinearorder _ _ _ Col_C_A_D) as (Col_A_C_D & Col_A_D_C & Col_D_C_A & Col_C_D_A & Col_D_A_C).

			contradict n_Col_A_C_D_and_Col_B_C_D.
			split.
			exact Col_A_C_D.
			exact Col_B_C_D.
		}
	}
	apply Classical_Prop.NNPP in eq_P_Q.

	exact eq_P_Q.
Qed.

End Euclid.
