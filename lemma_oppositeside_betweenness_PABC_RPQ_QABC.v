Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_eq_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.


Lemma lemma_oppositeside_betweenness_PABC_RPQ_QABC :
	forall A B C P Q R,
	OppositeSide P A B C ->
	BetS R P Q ->
	nCol R Q C ->
	Col A B R ->
	OppositeSide Q A B C.
Proof.
	intros A B C P Q R.
	intros OppositeSide_P_AB_C.
	intros BetS_R_P_Q.
	intros nCol_R_Q_C.
	intros Col_A_B_R.

	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_R_Q_C) as n_Col_R_Q_C.
	pose proof (by_prop_Col_order _ _ _ Col_A_B_R) as (Col_B_A_R & Col_B_R_A & Col_R_A_B & Col_A_R_B & Col_R_B_A).

	destruct OppositeSide_P_AB_C as (S & BetS_P_S_C & Col_A_B_S & nCol_A_B_P).
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_P) as n_Col_A_B_P.
	pose proof (by_prop_Col_order _ _ _ Col_A_B_S) as (Col_B_A_S & Col_B_S_A & Col_S_A_B & Col_A_S_B & Col_S_B_A).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_S_C) as BetS_C_S_P.
	pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_C_S_P BetS_R_P_Q nCol_R_Q_C) as (F & BetS_C_F_Q & BetS_R_S_F).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_R_S_F) as Col_R_S_F.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_P) as (neq_A_B & _ & _ & neq_B_A & _).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_B_R Col_A_B_S neq_A_B) as Col_B_R_S.
	pose proof (by_prop_Col_order _ _ _ Col_B_R_S) as (Col_R_B_S & Col_R_S_B & Col_S_B_R & Col_B_S_R & Col_S_R_B).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_R_S_F) as (neq_S_F & neq_R_S & neq_R_F).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_R_S_F Col_R_S_B neq_R_S) as Col_S_F_B.
	pose proof (by_prop_Col_order _ _ _ Col_S_F_B) as (Col_F_S_B & Col_F_B_S & Col_B_S_F & Col_S_B_F & Col_B_F_S).

	assert (Col A B F) as Col_A_B_F.
	assert (eq S B \/ neq S B) as [eq_S_B|neq_S_B] by (apply Classical_Prop.classic).
	{
		(* case eq_S_B *)
		pose proof (by_prop_eq_symmetric _ _ eq_S_B) as eq_B_S.
		assert (Col R B F) as Col_R_B_F by (rewrite eq_B_S; exact Col_R_S_F).
		assert (~ eq R B) as neq_R_B by (rewrite eq_B_S; exact neq_R_S).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_R_B_F Col_R_B_A neq_R_B) as Col_B_F_A.
		pose proof (by_prop_Col_order _ _ _ Col_B_F_A) as (Col_F_B_A & Col_F_A_B & Col_A_B_F & Col_B_A_F & Col_A_F_B).
		exact Col_A_B_F.
	}
	{
		(* case neq_S_B *)
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_S_B_A Col_S_B_F neq_S_B) as Col_B_A_F.
		pose proof (by_prop_Col_order _ _ _ Col_B_A_F) as (Col_A_B_F & Col_A_F_B & Col_F_B_A & Col_B_F_A & Col_F_A_B).
		exact Col_A_B_F.
	}
	pose proof (by_prop_Col_order _ _ _ Col_A_B_F) as (Col_B_A_F & Col_B_F_A & Col_F_A_B & Col_A_F_B & Col_F_B_A).

	assert (~ Col A B Q) as n_Col_A_B_Q.
	{
		intros Col_A_B_Q.

		pose proof (by_prop_Col_order _ _ _ Col_A_B_Q) as (Col_B_A_Q & Col_B_Q_A & Col_Q_A_B & Col_A_Q_B & Col_Q_B_A).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_B_Q Col_A_B_R neq_A_B) as Col_B_Q_R.
		pose proof (by_prop_Col_order _ _ _ Col_B_Q_R) as (Col_Q_B_R & Col_Q_R_B & Col_R_B_Q & Col_B_R_Q & Col_R_Q_B).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_B_R Col_A_B_F neq_A_B) as Col_B_R_F.

		assert (Col R Q F) as Col_R_Q_F.
		assert (eq B R \/ neq B R) as [eq_B_R|neq_B_R] by (apply Classical_Prop.classic).
		{
			(* case eq_B_R *)
			pose proof (by_prop_eq_symmetric _ _ eq_B_R) as eq_R_B.
			assert (neq A R) as neq_A_R by (rewrite eq_R_B; exact neq_A_B).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_A_R Col_B_A_F neq_B_A) as Col_A_R_F.
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_A_R Col_B_A_Q neq_B_A) as Col_A_R_Q.
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_R_F Col_A_R_Q neq_A_R) as Col_R_F_Q.
			pose proof (by_prop_Col_order _ _ _ Col_R_F_Q) as (Col_F_R_Q & Col_F_Q_R & Col_Q_R_F & Col_R_Q_F & Col_Q_F_R).
			exact Col_R_Q_F.
		}
		{
			(* case neq_B_R *)
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_R_Q Col_B_R_F neq_B_R) as Col_R_Q_F.
			exact Col_R_Q_F.
		}
		pose proof (by_prop_Col_order _ _ _ Col_R_Q_F) as (Col_Q_R_F & Col_Q_F_R & Col_F_R_Q & Col_R_F_Q & Col_F_Q_R).

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_F_Q) as Col_C_F_Q.
		pose proof (by_prop_Col_order _ _ _ Col_C_F_Q) as (Col_F_C_Q & Col_F_Q_C & Col_Q_C_F & Col_C_Q_F & Col_Q_F_C).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_C_F_Q) as (neq_F_Q & neq_C_F & neq_C_Q).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_F_Q_R Col_F_Q_C neq_F_Q) as Col_Q_R_C.
		pose proof (by_prop_Col_order _ _ _ Col_Q_R_C) as (Col_R_Q_C & Col_R_C_Q & Col_C_Q_R & Col_Q_C_R & Col_C_R_Q).

		contradict Col_R_Q_C.
		exact n_Col_R_Q_C.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_A_B_Q) as nCol_A_B_Q.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_F_Q) as BetS_Q_F_C.

	unfold OppositeSide.
	exists F.
	split.
	exact BetS_Q_F_C.
	split.
	exact Col_A_B_F.
	exact nCol_A_B_Q.
Qed.

End Euclid.
