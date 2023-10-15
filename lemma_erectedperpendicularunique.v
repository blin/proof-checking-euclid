Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
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
	intros RightTriangle_ABC.
	intros RightTriangle_ABE.
	intros SameSide_C_E_AB.

	assert (eq B B) as eq_B_B by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C A B B eq_B_B) as Col_A_B_B.

	assert (RightTriangle_ABC_2 := RightTriangle_ABC).
	destruct RightTriangle_ABC_2 as (_ & _ & _ & _ & neq_B_C).

	assert (SameSide_C_E_AB_2 := SameSide_C_E_AB).
	destruct SameSide_C_E_AB_2 as (_ & _ & _ & _ & _ & _ & _ & _ & nCol_A_B_E).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_E) as (neq_A_B & neq_B_E & neq_A_E & neq_B_A & neq_E_B & neq_E_A).

	pose proof (lemma_layoff _ _ _ _ neq_B_E neq_B_C) as (H & OnRay_BE_H & Cong_BH_BC).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BH_BC) as Cong_BC_BH.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BC_BH) as (Cong_CB_HB & _ & _).

	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_C_E_AB Col_A_B_B OnRay_BE_H) as SameSide_C_H_AB.

	pose proof (by_prop_RightTriangle_leg_change _ _ _ _ RightTriangle_ABE OnRay_BE_H) as RightTriangle_ABH.

	pose proof (
		lemma_right_triangle_same_base_cong_side_cong_hypotenuse _ _ _ _ RightTriangle_ABC RightTriangle_ABH Cong_BC_BH
	) as Cong_AC_AH.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AC_AH) as (Cong_CA_HA & _ & _).

	pose proof (proposition_07 _ _ _ _ neq_A_B Cong_CA_HA Cong_CB_HB SameSide_C_H_AB) as eq_C_H.

	assert (OnRay B E C) as OnRay_BE_C by (rewrite eq_C_H; exact OnRay_BE_H).
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_BE_C) as OnRay_BC_E.

	exact OnRay_BC_E.
Qed.

End Euclid.
