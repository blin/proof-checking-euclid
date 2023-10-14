Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Lt_asymmetric.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_Lt_transitive.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_OnRay_assert.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_CBA_n_ACB.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_collinear.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_legsmallerhypotenuse.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_BAC_BetS_ACB.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_altitudeofrighttriangle :
	forall A B C M p,
	RightTriangle B A C ->
	RightTriangle A M p ->
	Col B C p ->
	Col B C M ->
	BetS B M C.
Proof.
	intros A B C M p.
	intros RightTriangle_B_A_C.
	intros RightTriangle_A_M_p.
	intros Col_B_C_p.
	intros Col_B_C_M.

	pose proof (cn_congruencereflexive B C) as Cong_B_C_B_C.
	pose proof (cn_congruencereflexive C B) as Cong_C_B_C_B.
	pose proof (cn_congruencereverse B A) as Cong_B_A_A_B.
	pose proof (cn_congruencereverse C B) as Cong_C_B_B_C.
	pose proof (cn_congruencereverse M B) as Cong_M_B_B_M.
	pose proof (cn_congruencereverse M C) as Cong_M_C_C_M.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_B_A_C) as RightTriangle_C_A_B.
	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_B_A_C) as nCol_B_A_C.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_A_C) as (_ & _ & _ & _ & _ & neq_C_B).
	pose proof (by_prop_neq_symmetric _ _ neq_C_B) as neq_B_C.

	pose proof (by_prop_RightTriangle_legsmallerhypotenuse _ _ _ RightTriangle_B_A_C) as (Lt_B_A_B_C & Lt_A_C_B_C).

	pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_B_A_B_C Cong_B_A_A_B) as Lt_A_B_B_C.

	pose proof (by_prop_RightTriangle_CBA_n_ACB _ _ _ RightTriangle_B_A_C) as n_RightTriangle_C_B_A.
	pose proof (by_prop_RightTriangle_CBA_n_ACB _ _ _ RightTriangle_C_A_B) as n_RightTriangle_B_C_A.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_A_M_p) as RightTriangle_p_M_A.
	
	pose proof (by_prop_Col_order _ _ _ Col_B_C_p) as (Col_C_B_p & Col_C_p_B & Col_p_B_C & Col_B_p_C & Col_p_C_B).

	pose proof (by_prop_Col_order _ _ _ Col_B_C_M) as (Col_C_B_M & Col_C_M_B & Col_M_B_C & Col_B_M_C & Col_M_C_B).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_B_p Col_C_B_M neq_C_B) as Col_B_p_M.
	pose proof (by_prop_Col_order _ _ _ Col_B_p_M) as (_ & Col_p_M_B & _ & _ & _).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_C_p Col_B_C_M neq_B_C) as Col_C_p_M.
	pose proof (by_prop_Col_order _ _ _ Col_C_p_M) as (_ & Col_p_M_C & _ & _ & _).

	assert (~ eq B M) as n_eq_B_M.
	{
		intro eq_B_M.

		assert (RightTriangle A B p) as RightTriangle_A_B_p by (rewrite eq_B_M; exact RightTriangle_A_M_p).
		pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_A_B_p) as RightTriangle_p_B_A.
		pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_p_B_A Col_p_B_C neq_C_B) as RightTriangle_C_B_A.

		contradict RightTriangle_C_B_A.
		exact n_RightTriangle_C_B_A.
	}
	assert (neq_B_M := n_eq_B_M).

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_p_M_A Col_p_M_B neq_B_M) as RightTriangle_B_M_A.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_B_M_A) as RightTriangle_A_M_B.
	pose proof (by_prop_RightTriangle_legsmallerhypotenuse _ _ _ RightTriangle_A_M_B) as (_ & Lt_M_B_A_B).
	pose proof (by_prop_Lt_transitive _ _ _ _ _ _ Lt_M_B_A_B Lt_A_B_B_C) as Lt_M_B_B_C.
	pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_M_B_B_C Cong_M_B_B_M) as Lt_B_M_B_C.

	assert (~ eq C M) as n_eq_C_M.
	{
		intro eq_C_M.

		assert (RightTriangle A C p) as RightTriangle_A_C_p by (rewrite eq_C_M; exact RightTriangle_A_M_p).
		pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_A_C_p) as RightTriangle_p_C_A.
		pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_p_C_A Col_p_C_B neq_B_C) as RightTriangle_B_C_A.

		contradict RightTriangle_B_C_A.
		exact n_RightTriangle_B_C_A.
	}
	assert (neq_C_M := n_eq_C_M).


	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_p_M_A Col_p_M_C neq_C_M) as RightTriangle_C_M_A.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_C_M_A) as RightTriangle_A_M_C.
	pose proof (by_prop_RightTriangle_legsmallerhypotenuse _ _ _ RightTriangle_A_M_C) as (_ & Lt_M_C_A_C).
	pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_M_C_A_C Cong_M_C_C_M) as Lt_C_M_A_C.
	pose proof (by_prop_Lt_transitive _ _ _ _ _ _ Lt_C_M_A_C Lt_A_C_B_C) as Lt_C_M_B_C.

	assert (~ BetS M B C) as n_BetS_M_B_C.
	{
		intro BetS_M_B_C.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_M_B_C) as BetS_C_B_M.
		pose proof (by_def_Lt _ _ _ _ _ BetS_C_B_M Cong_C_B_C_B) as Lt_C_B_C_M.
		pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_C_B_C_M Cong_C_B_B_C) as Lt_B_C_C_M.
		pose proof (by_prop_Lt_asymmetric _ _ _ _ Lt_B_C_C_M) as n_Lt_C_M_B_C.

		contradict Lt_C_M_B_C.
		exact n_Lt_C_M_B_C.
	}

	(* assert by cases *)
	assert (OnRay B C M) as OnRay_B_C_M.
	assert (Col_B_C_M_2 := Col_B_C_M).
	destruct Col_B_C_M_2 as [eq_B_C | [eq_B_M | [eq_C_M | [BetS_C_B_M | [BetS_B_C_M | BetS_B_M_C]]]]].
	{
		(* case eq_B_C *)
		contradict eq_B_C.
		exact neq_B_C.
	}
	{
		(* case eq_B_M *)
		contradict eq_B_M.
		exact neq_B_M.
	}
	{
		(* case eq_C_M *)
		contradict eq_C_M.
		exact neq_C_M.
	}
	{
		(* case BetS_C_B_M *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_B_M) as BetS_M_B_C.

		contradict BetS_M_B_C.
		exact n_BetS_M_B_C.
	}
	{
		(* case BetS_B_C_M *)
		
		pose proof (by_def_OnRay_from_BetS_A_B_E B C M BetS_B_C_M neq_B_C) as OnRay_B_C_M.

		exact OnRay_B_C_M.
	}
	{
		(* case BetS_B_M_C *)
		
		pose proof (by_def_OnRay_from_BetS_A_B_E B M C BetS_B_M_C neq_B_M) as OnRay_B_M_C.

		pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_B_M_C) as OnRay_B_C_M.

		exact OnRay_B_C_M.
	}

	assert (~ BetS B C M) as n_BetS_B_C_M.
	{
		intro BetS_B_C_M.

		pose proof (by_def_Lt _ _ _ _ _ BetS_B_C_M Cong_B_C_B_C) as Lt_B_C_B_M.
		pose proof (by_prop_Lt_asymmetric _ _ _ _ Lt_B_C_B_M) as n_Lt_B_M_B_C.

		contradict Lt_B_M_B_C.
		exact n_Lt_B_M_B_C.
	}

	(* assert by cases *)
	assert (OnRay C B M) as OnRay_C_B_M.
	assert (Col_B_C_M_2 := Col_B_C_M).
	destruct Col_B_C_M_2 as [eq_B_C | [eq_B_M | [eq_C_M | [BetS_C_B_M | [BetS_B_C_M | BetS_B_M_C]]]]].
	{
		(* case eq_B_C *)
		contradict eq_B_C.
		exact neq_B_C.
	}
	{
		(* case eq_B_M *)
		contradict eq_B_M.
		exact neq_B_M.
	}
	{
		(* case eq_C_M *)
		contradict eq_C_M.
		exact neq_C_M.
	}
	{
		(* case BetS_C_B_M *)
		pose proof (by_def_OnRay_from_BetS_A_B_E C B M BetS_C_B_M neq_C_B) as OnRay_C_B_M.

		exact OnRay_C_B_M.
	}
	{
		(* case BetS_B_C_M *)
		contradict BetS_B_C_M.
		exact n_BetS_B_C_M.
	}
	{
		(* case BetS_B_M_C *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_C) as BetS_C_M_B.
		
		pose proof (by_def_OnRay_from_BetS_A_B_E C M B BetS_C_M_B neq_C_M) as OnRay_C_M_B.
		pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_C_M_B) as OnRay_C_B_M.

		exact OnRay_C_B_M.
	}
	pose proof (by_prop_OnRay_ABC_BAC_BetS_ACB _ _ _ OnRay_B_C_M OnRay_C_B_M) as BetS_B_M_C.

	exact BetS_B_M_C.
Qed.

End Euclid.
