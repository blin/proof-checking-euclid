Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_SumTwoRT.
Require Import ProofCheckingEuclid.by_def_Supp.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_13 :
	forall A B C D,
	BetS D B C ->
	nCol A B C ->
	SumTwoRT C B A A B D.
Proof.
	intros A B C D.
	intros BetS_D_B_C.
	intros nCol_A_B_C.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_D_B_C) as (_ & neq_D_B & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_B_C) as BetS_C_B_D.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_B_D) as Col_C_B_D.

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (_ & _ & _ & neq_B_A & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (_ & _ & _ & _ & nCol_C_B_A).

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_A) as OnRay_BA_A.

	assert (eq B B) as eq_B_B by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C C B B eq_B_B) as Col_C_B_B.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_C_B_A Col_C_B_D Col_C_B_B neq_D_B) as nCol_D_B_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_D_B_A) as (_ & _ & _ & _ & nCol_A_B_D).

	pose proof (by_prop_CongA_reflexive _ _ _ nCol_A_B_D) as CongA_ABD_ABD.
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_C_B_A) as CongA_CBA_CBA.

	pose proof (by_def_Supp _ _ _ _ _ OnRay_BA_A BetS_C_B_D) as Supp_CBA_ABD.

	pose proof (by_def_SumTwoRT _ _ _ _ _ _ _ _ _ _ _ Supp_CBA_ABD CongA_CBA_CBA CongA_ABD_ABD) as SumTwoRT_CBA_ABD.

	exact SumTwoRT_CBA_ABD.
Qed.

End Euclid.
