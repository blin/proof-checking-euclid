Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol .
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Cross.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_Par.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_def_Rectangle.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_CBA_n_ACB.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_collinear.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_rectangleparallelogram :
	forall A B C D,
	Rectangle A B C D ->
	Parallelogram A B C D.
Proof.
	intros A B C D.
	intros Rectangle_A_B_C_D.


	destruct Rectangle_A_B_C_D as (RightTriangle_D_A_B & RightTriangle_A_B_C & RightTriangle_B_C_D & RightTriangle_C_D_A & Cross_A_C_B_D).
	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_D_A_B) as nCol_D_A_B.
	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_A_B_C) as nCol_A_B_C.
	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_C_D_A) as nCol_C_D_A.
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_C_D_A) as n_Col_C_D_A.
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_D_A_B) as n_Col_D_A_B.
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_C) as n_Col_A_B_C.

	destruct Cross_A_C_B_D as (M & BetS_A_M_C & BetS_B_M_D).

	assert (~ Meet A B C D) as n_Meet_A_B_C_D.
	{
		intro Meet_A_B_C_D.

		destruct Meet_A_B_C_D as (P & neq_A_B & neq_C_D & Col_A_B_P & Col_C_D_P).

		assert (~ eq A P) as n_eq_A_P.
		{
			intro eq_A_P.
			assert (Col C D A) as Col_C_D_A by (rewrite eq_A_P; exact Col_C_D_P).
			contradict Col_C_D_A.
			exact n_Col_C_D_A.
		}
		assert (neq_A_P := n_eq_A_P).

		assert (~ eq D P) as n_eq_D_P.
		{
			intro eq_D_P.
			assert (Col A B D) as Col_A_B_D by (rewrite eq_D_P; exact Col_A_B_P).
			pose proof (by_prop_Col_order _ _ _ Col_A_B_D) as (_ & _ & Col_D_A_B & _ & _).
			contradict Col_D_A_B.
			exact n_Col_D_A_B.
		}
		assert (neq_D_P := n_eq_D_P).


		pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_D_A_B) as RightTriangle_B_A_D.
		pose proof (by_prop_Col_order _ _ _ Col_A_B_P) as (Col_B_A_P & _ & _ & _ & _).
		pose proof (by_prop_neq_symmetric _ _ neq_A_P) as neq_P_A.
		pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_B_A_D Col_B_A_P neq_P_A) as RightTriangle_P_A_D.
		pose proof (by_prop_neq_symmetric _ _ neq_D_P) as neq_P_D.
		pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_C_D_A Col_C_D_P neq_P_D) as RightTriangle_P_D_A.
		pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_P_D_A) as RightTriangle_A_D_P.
		pose proof (by_prop_RightTriangle_CBA_n_ACB _ _ _ RightTriangle_A_D_P) as n_RightTriangle_P_A_D.
		contradict RightTriangle_P_A_D.
		exact n_RightTriangle_P_A_D.
	}

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & _ & _ & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_C_D_A) as (neq_C_D & _ & _ & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_C_D_A) as (_ & _ & _ & neq_D_C & _ & _).
	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C A B A eq_A_A) as Col_A_B_A.
	assert (eq B B) as eq_B_B by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C A B B eq_B_B) as Col_A_B_B.
	assert (eq C C) as eq_C_C by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C C D C eq_C_C) as Col_C_D_C.
	assert (eq D D) as eq_D_D by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C C D D eq_D_D) as Col_C_D_D.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_D) as BetS_D_M_B.
	pose proof (by_def_Par _ _ _ _ _ _ _ _ _ neq_A_B neq_C_D Col_A_B_A Col_A_B_B neq_A_B Col_C_D_D Col_C_D_C neq_D_C n_Meet_A_B_C_D BetS_A_M_C BetS_D_M_B) as Par_A_B_C_D.

	assert (~ Meet A D B C) as n_Meet_A_D_B_C.
	{
		intro Meet_A_D_B_C.

		destruct Meet_A_D_B_C as (P & neq_A_D & neq_B_C & Col_A_D_P & Col_B_C_P).

		assert (~ eq A P) as n_eq_A_P.
		{
			intro eq_A_P.
			assert (Col B C A) as Col_B_C_A by (rewrite eq_A_P; exact Col_B_C_P).
			pose proof (by_prop_Col_order _ _ _ Col_B_C_A) as (_ & _ & Col_A_B_C & _ & _).
			contradict Col_A_B_C.
			exact n_Col_A_B_C.
		}
		assert (neq_A_P := n_eq_A_P).



		assert (~ eq B P) as n_eq_B_P.
		{
			intro eq_B_P.
			assert (Col A D B) as Col_A_D_B by (rewrite eq_B_P; exact Col_A_D_P).
			pose proof (by_prop_Col_order _ _ _ Col_A_D_B) as (Col_D_A_B & _ & _ & _ & _).
			contradict Col_D_A_B.
			exact n_Col_D_A_B.
		}
		assert (neq_B_P := n_eq_B_P).


		pose proof (by_prop_neq_symmetric _ _ neq_A_P) as neq_P_A.
		pose proof (by_prop_Col_order _ _ _ Col_A_D_P) as (Col_D_A_P & _ & _ & _ & _).
		pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_D_A_B Col_D_A_P neq_P_A) as RightTriangle_P_A_B.
		pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_A_B_C) as RightTriangle_C_B_A.
		pose proof (by_prop_Col_order _ _ _ Col_B_C_P) as (Col_C_B_P & _ & _ & _ & _).
		pose proof (by_prop_neq_symmetric _ _ neq_B_P) as neq_P_B.
		pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_C_B_A Col_C_B_P neq_P_B) as RightTriangle_P_B_A.
		pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_P_A_B) as RightTriangle_B_A_P.
		pose proof (by_prop_RightTriangle_CBA_n_ACB _ _ _ RightTriangle_B_A_P) as n_RightTriangle_P_B_A.
		contradict RightTriangle_P_B_A.
		exact n_RightTriangle_P_B_A.
	}

	pose proof (by_prop_nCol_distinct _ _ _ nCol_D_A_B) as (_ & _ & _ & neq_A_D & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (_ & neq_B_C & _ & _ & _ & _).
	pose proof (by_def_Col_from_eq_A_C A D A eq_A_A) as Col_A_D_A.
	pose proof (by_def_Col_from_eq_B_C A D D eq_D_D) as Col_A_D_D.
	pose proof (by_def_Col_from_eq_A_C B C B eq_B_B) as Col_B_C_B.
	pose proof (by_def_Col_from_eq_B_C B C C eq_C_C) as Col_B_C_C.
	pose proof (by_def_Par _ _ _ _ _ _ _ _ _ neq_A_D neq_B_C Col_A_D_A Col_A_D_D neq_A_D Col_B_C_B Col_B_C_C neq_B_C n_Meet_A_D_B_C BetS_A_M_C BetS_B_M_D) as Par_A_D_B_C.
	pose proof (by_def_Parallelogram _ _ _ _ Par_A_B_C_D Par_A_D_B_C) as Parallelogram_A_B_C_D.

	exact Parallelogram_A_B_C_D.
Qed.

End Euclid.
