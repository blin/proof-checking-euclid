Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Lt_asymmetric.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_Lt_transitive.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_BAC_BetS_ACB.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_CBA_n_ACB.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_collinear.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_legsmallerhypotenuse.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

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
	intros RightTriangle_BAC.
	intros RightTriangle_AMp.
	intros Col_B_C_p.
	intros Col_B_C_M.

	pose proof (cn_congruencereflexive B C) as Cong_BC_BC.
	pose proof (cn_congruencereflexive C B) as Cong_CB_CB.
	pose proof (cn_congruencereverse B A) as Cong_BA_AB.
	pose proof (cn_congruencereverse C B) as Cong_CB_BC.
	pose proof (cn_congruencereverse M B) as Cong_MB_BM.
	pose proof (cn_congruencereverse M C) as Cong_MC_CM.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_BAC) as RightTriangle_CAB.
	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_BAC) as nCol_B_A_C.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_A_C) as (_ & _ & _ & _ & _ & neq_C_B).
	pose proof (by_prop_neq_symmetric _ _ neq_C_B) as neq_B_C.

	pose proof (by_prop_RightTriangle_legsmallerhypotenuse _ _ _ RightTriangle_BAC) as (Lt_BA_BC & Lt_AC_BC).

	pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_BA_BC Cong_BA_AB) as Lt_AB_BC.

	pose proof (by_prop_RightTriangle_CBA_n_ACB _ _ _ RightTriangle_BAC) as n_RightTriangle_CBA.
	pose proof (by_prop_RightTriangle_CBA_n_ACB _ _ _ RightTriangle_CAB) as n_RightTriangle_BCA.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_AMp) as RightTriangle_pMA.

	pose proof (by_prop_Col_order _ _ _ Col_B_C_p) as (Col_C_B_p & Col_C_p_B & Col_p_B_C & Col_B_p_C & Col_p_C_B).

	pose proof (by_prop_Col_order _ _ _ Col_B_C_M) as (Col_C_B_M & Col_C_M_B & Col_M_B_C & Col_B_M_C & Col_M_C_B).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_B_p Col_C_B_M neq_C_B) as Col_B_p_M.
	pose proof (by_prop_Col_order _ _ _ Col_B_p_M) as (_ & Col_p_M_B & _ & _ & _).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_C_p Col_B_C_M neq_B_C) as Col_C_p_M.
	pose proof (by_prop_Col_order _ _ _ Col_C_p_M) as (_ & Col_p_M_C & _ & _ & _).

	assert (~ eq B M) as n_eq_B_M.
	{
		intro eq_B_M.

		assert (RightTriangle A B p) as RightTriangle_ABp by (rewrite eq_B_M; exact RightTriangle_AMp).
		pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_ABp) as RightTriangle_pBA.
		pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_pBA Col_p_B_C neq_C_B) as RightTriangle_CBA.

		contradict RightTriangle_CBA.
		exact n_RightTriangle_CBA.
	}
	assert (neq_B_M := n_eq_B_M).

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_pMA Col_p_M_B neq_B_M) as RightTriangle_BMA.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_BMA) as RightTriangle_AMB.
	pose proof (by_prop_RightTriangle_legsmallerhypotenuse _ _ _ RightTriangle_AMB) as (_ & Lt_MB_AB).
	pose proof (by_prop_Lt_transitive _ _ _ _ _ _ Lt_MB_AB Lt_AB_BC) as Lt_MB_BC.
	pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_MB_BC Cong_MB_BM) as Lt_BM_BC.

	assert (~ eq C M) as n_eq_C_M.
	{
		intro eq_C_M.

		assert (RightTriangle A C p) as RightTriangle_ACp by (rewrite eq_C_M; exact RightTriangle_AMp).
		pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_ACp) as RightTriangle_pCA.
		pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_pCA Col_p_C_B neq_B_C) as RightTriangle_BCA.

		contradict RightTriangle_BCA.
		exact n_RightTriangle_BCA.
	}
	assert (neq_C_M := n_eq_C_M).


	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_pMA Col_p_M_C neq_C_M) as RightTriangle_CMA.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_CMA) as RightTriangle_AMC.
	pose proof (by_prop_RightTriangle_legsmallerhypotenuse _ _ _ RightTriangle_AMC) as (_ & Lt_MC_AC).
	pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_MC_AC Cong_MC_CM) as Lt_CM_AC.
	pose proof (by_prop_Lt_transitive _ _ _ _ _ _ Lt_CM_AC Lt_AC_BC) as Lt_CM_BC.

	assert (~ BetS M B C) as n_BetS_M_B_C.
	{
		intro BetS_M_B_C.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_M_B_C) as BetS_C_B_M.
		pose proof (by_def_Lt _ _ _ _ _ BetS_C_B_M Cong_CB_CB) as Lt_CB_CM.
		pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_CB_CM Cong_CB_BC) as Lt_BC_CM.
		pose proof (by_prop_Lt_asymmetric _ _ _ _ Lt_BC_CM) as n_Lt_CM_BC.

		contradict Lt_CM_BC.
		exact n_Lt_CM_BC.
	}

	(* assert by cases *)
	assert (OnRay B C M) as OnRay_BC_M.
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

		pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_C_M neq_B_C) as OnRay_BC_M.

		exact OnRay_BC_M.
	}
	{
		(* case BetS_B_M_C *)

		pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_M_C neq_B_M) as OnRay_BM_C.

		pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_BM_C) as OnRay_BC_M.

		exact OnRay_BC_M.
	}

	assert (~ BetS B C M) as n_BetS_B_C_M.
	{
		intro BetS_B_C_M.

		pose proof (by_def_Lt _ _ _ _ _ BetS_B_C_M Cong_BC_BC) as Lt_BC_BM.
		pose proof (by_prop_Lt_asymmetric _ _ _ _ Lt_BC_BM) as n_Lt_BM_BC.

		contradict Lt_BM_BC.
		exact n_Lt_BM_BC.
	}

	(* assert by cases *)
	assert (OnRay C B M) as OnRay_CB_M.
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
		pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_C_B_M neq_C_B) as OnRay_CB_M.

		exact OnRay_CB_M.
	}
	{
		(* case BetS_B_C_M *)
		contradict BetS_B_C_M.
		exact n_BetS_B_C_M.
	}
	{
		(* case BetS_B_M_C *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_C) as BetS_C_M_B.

		pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_C_M_B neq_C_M) as OnRay_CM_B.
		pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_CM_B) as OnRay_CB_M.

		exact OnRay_CB_M.
	}
	pose proof (by_prop_OnRay_ABC_BAC_BetS_ACB _ _ _ OnRay_BC_M OnRay_CB_M) as BetS_B_M_C.

	exact BetS_B_M_C.
Qed.

End Euclid.
