Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_OnRay.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_RightTriangle.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_leg_change.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma by_prop_RightTriangle_collinear :
	forall A B C D,
	RightTriangle A B D ->
	Col A B C ->
	neq C B ->
	RightTriangle C B D.
Proof.
	intros A B C D.
	intros RightTriangle_ABD.
	intros Col_A_B_C.
	intros neq_C_B.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_ABD) as RightTriangle_DBA.

	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_ABD) as nCol_A_B_D.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_D) as (neq_A_B & neq_B_D & _ & neq_B_A & _ & _).

	pose proof (by_prop_neq_symmetric _ _ neq_C_B) as neq_B_C.

	destruct RightTriangle_ABD as (E & BetS_A_B_E & Cong_AB_EB & Cong_AD_ED & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_E) as BetS_E_B_A.

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AB_EB) as Cong_EB_AB.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AD_ED) as Cong_ED_AD.

	pose proof (by_def_RightTriangle _ _ _ _ BetS_E_B_A Cong_EB_AB Cong_ED_AD neq_B_D) as RightTriangle_EBD.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_EBD) as RightTriangle_DBE.

	assert (RightTriangle D B C) as RightTriangle_DBC.
	destruct Col_A_B_C as [eq_A_B | [eq_A_C | [eq_B_C | [BetS_B_A_C | [BetS_A_B_C | BetS_A_C_B]]]]].
	{
		(* case eq_A_B *)
		contradict eq_A_B.
		exact neq_A_B.
	}
	{
		(* case eq_A_C *)
		assert (RightTriangle D B C) as RightTriangle_DBC by (rewrite <- eq_A_C; exact RightTriangle_DBA).

		exact RightTriangle_DBC.
	}
	{
		(* case eq_B_C *)
		contradict eq_B_C.
		exact neq_B_C.
	}
	{
		(* case BetS_B_A_C *)
		pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_A_C neq_B_A) as OnRay_BA_C.
		pose proof (by_prop_RightTriangle_leg_change _ _ _ _ RightTriangle_DBA OnRay_BA_C) as RightTriangle_DBC.

		exact RightTriangle_DBC.
	}
	{
		(* case BetS_A_B_C *)
		pose proof (by_def_OnRay _ _ _ _ BetS_A_B_E BetS_A_B_C) as OnRay_BE_C.
		pose proof (by_prop_RightTriangle_leg_change _ _ _ _ RightTriangle_DBE OnRay_BE_C) as RightTriangle_DBC.

		exact RightTriangle_DBC.
	}
	{
		(* case BetS_A_C_B *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_B) as BetS_B_C_A.
		pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_C_A neq_B_C) as OnRay_BC_A.
		pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_BC_A) as OnRay_BA_C.
		pose proof (by_prop_RightTriangle_leg_change _ _ _ _ RightTriangle_DBA OnRay_BA_C) as RightTriangle_DBC.

		exact RightTriangle_DBC.
	}

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_DBC) as RightTriangle_CBD.

	exact RightTriangle_CBD.
Qed.

End Euclid.
