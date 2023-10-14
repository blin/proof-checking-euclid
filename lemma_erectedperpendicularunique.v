Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_RightTriangle.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_leg_change.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct .
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_right_triangle_same_base_cong_side_cong_hypotenuse.
Require Import ProofCheckingEuclid.lemma_sameside_onray_EFAC_BFG_EGAC.
Require Import ProofCheckingEuclid.proposition_07.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_erectedperpendicularunique :
	forall A B C E,
	RightTriangle A B C ->
	RightTriangle A B E ->
	SameSide C E A B ->
	OnRay B C E.
Proof.
	intros A B C E.
	intros RightTriangle_A_B_C.
	intros RightTriangle_A_B_E.
	intros SameSide_C_E_A_B.

	assert (eq B B) as eq_B_B by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C A B B eq_B_B) as Col_A_B_B.

	assert (RightTriangle_A_B_C_2 := RightTriangle_A_B_C).
	destruct RightTriangle_A_B_C_2 as (_ & _ & _ & _ & neq_B_C).
	
	assert (SameSide_C_E_A_B_2 := SameSide_C_E_A_B).
	destruct SameSide_C_E_A_B_2 as (_ & _ & _ & _ & _ & _ & _ & _ & nCol_A_B_E).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_E) as (neq_A_B & neq_B_E & neq_A_E & neq_B_A & neq_E_B & neq_E_A).

	pose proof (lemma_layoff _ _ _ _ neq_B_E neq_B_C) as (H & OnRay_B_E_H & Cong_B_H_B_C).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_B_H_B_C) as Cong_B_C_B_H.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_B_C_B_H) as (Cong_C_B_H_B & _ & _).

	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_C_E_A_B Col_A_B_B OnRay_B_E_H) as SameSide_C_H_A_B.

	pose proof (by_prop_RightTriangle_leg_change _ _ _ _ RightTriangle_A_B_E OnRay_B_E_H) as RightTriangle_A_B_H.

	pose proof (
		lemma_right_triangle_same_base_cong_side_cong_hypotenuse _ _ _ _ RightTriangle_A_B_C RightTriangle_A_B_H Cong_B_C_B_H
	) as Cong_A_C_A_H.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_A_C_A_H) as (Cong_C_A_H_A & _ & _).

	pose proof (proposition_07 _ _ _ _ neq_A_B Cong_C_A_H_A Cong_C_B_H_B SameSide_C_H_A_B) as eq_C_H.

	assert (OnRay B E C) as OnRay_B_E_C by (rewrite eq_C_H; exact OnRay_B_E_H).
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_B_E_C) as OnRay_B_C_E.

	exact OnRay_B_C_E.
Qed.

End Euclid.
