Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_def_RightTriangle.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_doublereverse.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_OnRay_assert.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.proposition_16.
Require Import ProofCheckingEuclid.proposition_19.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_RightTriangle_legsmallerhypotenuse :
	forall A B C,
	RightTriangle A B C ->
	Lt A B A C /\ Lt B C A C.
Proof.
	intros A B C.
	intros RightTriangle_A_B_C.

	pose proof (cn_congruencereflexive B A) as Cong_B_A_B_A.
	pose proof (cn_congruencereverse C A) as Cong_C_A_A_C.
	pose proof (cn_congruencereverse C B) as Cong_C_B_B_C.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_A_B_C) as RightTriangle_C_B_A.
	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_A_B_C) as nCol_A_B_C.

	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).

	pose proof (by_def_Triangle _ _ _ nCol_A_B_C) as Triangle_A_B_C.
	pose proof (by_def_Triangle _ _ _ nCol_A_C_B) as Triangle_A_C_B.
	pose proof (by_def_Triangle _ _ _ nCol_C_B_A) as Triangle_C_B_A.

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_A_C) as CongA_B_A_C_C_A_B.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_C_B_A) as CongA_C_B_A_A_B_C.

	pose proof (by_def_OnRay_from_neq_A_B B A neq_B_A) as OnRay_B_A_A.
	pose proof (by_def_OnRay_from_neq_A_B B C neq_B_C) as OnRay_B_C_C.

	destruct RightTriangle_C_B_A as (D & BetS_C_B_D & Cong_C_B_D_B & Cong_C_A_D_A & _).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_B_D) as (neq_B_D & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_B_D) as neq_D_B.
	pose proof (by_def_Col_from_BetS_A_B_C C B D BetS_C_B_D) as Col_C_B_D.
	pose proof (by_prop_Col_order _ _ _ Col_C_B_D) as (_ & _ & _ & _ & Col_D_B_C).

	pose proof (by_def_OnRay_from_neq_A_B B D neq_B_D) as OnRay_B_D_D.

	pose proof (by_prop_Cong_doublereverse _ _ _ _ Cong_C_B_D_B) as (Cong_B_D_B_C & _).
	pose proof (by_prop_Cong_doublereverse _ _ _ _ Cong_C_A_D_A) as (Cong_A_D_A_C & _).

	assert (~ Col A B D) as n_Col_A_B_D.
	{
		intro Col_A_B_D.

		pose proof (by_prop_Col_order _ _ _ Col_A_B_D) as (_ & _ & _ & _ & Col_D_B_A).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_B_C Col_D_B_A neq_D_B) as Col_B_C_A.
		pose proof (by_prop_Col_order _ _ _ Col_B_C_A) as (_ & _ & Col_A_B_C & _ & _).
		
		pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_C) as n_Col_A_B_C.

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_A_B_D) as nCol_A_B_D.

	pose proof (
		by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_B_A_A OnRay_B_D_D OnRay_B_A_A OnRay_B_C_C Cong_B_A_B_A Cong_B_D_B_C Cong_A_D_A_C nCol_A_B_D
	) as CongA_A_B_D_A_B_C.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_A_B_D_A_B_C) as CongA_A_B_C_A_B_D.

	pose proof (proposition_16 _ _ _ _ Triangle_A_C_B BetS_C_B_D) as (LtA_C_A_B_A_B_D & LtA_B_C_A_A_B_D).

	pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_C_A_B_A_B_D CongA_A_B_C_A_B_D) as LtA_C_A_B_A_B_C.
	pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_B_C_A_A_B_D CongA_A_B_C_A_B_D) as LtA_B_C_A_A_B_C.
	pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_C_A_B_A_B_C CongA_B_A_C_C_A_B) as LtA_B_A_C_A_B_C.
	pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_B_A_C_A_B_C CongA_C_B_A_A_B_C) as LtA_B_A_C_C_B_A.

	pose proof (proposition_19 _ _ _ Triangle_A_B_C LtA_B_C_A_A_B_C) as Lt_A_B_A_C.
	pose proof (proposition_19 _ _ _ Triangle_C_B_A LtA_B_A_C_C_B_A) as Lt_C_B_C_A.

	pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_C_B_C_A Cong_C_B_B_C) as Lt_B_C_C_A.
	pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_B_C_C_A Cong_C_A_A_C) as Lt_B_C_A_C.

	split.
	exact Lt_A_B_A_C.
	exact Lt_B_C_A_C.
Qed.

End Euclid.
