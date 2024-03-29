Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B .
Require Import ProofCheckingEuclid.by_def_SumTwoRT.
Require Import ProofCheckingEuclid.by_def_Supp.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_collinear.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct .
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Euclid4.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.proposition_14.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_righttogether :
	forall A B C G,
	RightTriangle G A B ->
	RightTriangle B A C ->
	OppositeSide G B A C ->
	SumTwoRT G A B B A C /\ BetS G A C.
Proof.
	intros A B C G.
	intros RightTriangle_GAB.
	intros RightTriangle_BAC.
	intros OppositeSide_G_BA_C.

	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_G_BA_C) as OppositeSide_C_BA_G.

	assert (OppositeSide_G_BA_C_2 := OppositeSide_G_BA_C).
	destruct OppositeSide_G_BA_C_2 as (_ & _ & _ & nCol_B_A_G).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_A_G) as (neq_B_A & neq_A_G & neq_B_G & neq_A_B & neq_G_A & neq_G_B).
	pose proof (by_prop_nCol_order _ _ _ nCol_B_A_G) as (_ & _ & _ & _ & nCol_G_A_B).
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_G_A_B) as CongA_GAB_GAB.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_A_B) as OnRay_AB_B.

	pose proof (lemma_extension _ _ _ _ neq_G_A neq_G_A) as (D & BetS_G_A_D & _).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_G_A_D) as (neq_A_D & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_A_D) as neq_D_A.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_G_A_D) as Col_G_A_D.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_AB_B BetS_G_A_D) as Supp_GAB_BAD.

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_GAB Col_G_A_D neq_D_A) as RightTriangle_DAB.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_DAB) as RightTriangle_BAD.

	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_BAC RightTriangle_BAD) as CongA_BAC_BAD.

	pose proof (by_def_SumTwoRT _ _ _ _ _ _ _ _ _ _ _ Supp_GAB_BAD CongA_GAB_GAB CongA_BAC_BAD) as SumTwoRT_GAB_BAC.

	pose proof (proposition_14 _ _ _ _ _ SumTwoRT_GAB_BAC OnRay_AB_B OppositeSide_C_BA_G) as (_ & BetS_G_A_C).

	split.
	exact SumTwoRT_GAB_BAC.
	exact BetS_G_A_C.
Qed.

End Euclid.
