Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_Supp.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_distinct.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_Supp_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_supplements_conga.
Require Import ProofCheckingEuclid.proposition_27.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_28B :
	forall A B C D G H,
	BetS A G B ->
	BetS C H D ->
	SumTwoRT B G H G H D ->
	SameSide B D G H ->
	Par A B C D.
Proof.
	intros A B C D G H.
	intros BetS_A_G_B.
	intros BetS_C_H_D.
	intros SumTwoRT_BGH_GHD.
	intros SameSide_B_D_GH.

	assert (eq G G) as eq_G_G by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C G H G eq_G_G) as Col_G_H_G.

	destruct SumTwoRT_BGH_GHD as (a & b & c & d & e & Supp_abc_ebd & CongA_BGH_abc & CongA_GHD_ebd).

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_BGH_abc) as CongA_abc_BGH.

	pose proof (by_prop_CongA_distinct _ _ _ _ _ _ CongA_GHD_ebd) as (neq_G_H & _ & _ & _ & _ & _).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_B_D_GH) as (SameSide_D_B_GH & _ & _).

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_G_H) as OnRay_GH_H.

	pose proof (by_def_Supp _ _ _ _ _ OnRay_GH_H BetS_A_G_B) as Supp_AGH_HGB.
	pose proof (by_prop_Supp_symmetric _ _ _ _ _ Supp_AGH_HGB) as Supp_BGH_HGA.


	pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_abc_BGH Supp_abc_ebd Supp_BGH_HGA) as CongA_ebd_HGA.

	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_ebd_HGA) as nCol_H_G_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_H_G_A) as (nCol_G_H_A & nCol_G_A_H & nCol_A_H_G & nCol_H_A_G & nCol_A_G_H).

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_H_G_A) as CongA_HGA_AGH.

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_GHD_ebd CongA_ebd_HGA) as CongA_GHD_HGA.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_GHD_HGA CongA_HGA_AGH) as CongA_GHD_AGH.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_GHD_AGH) as CongA_AGH_GHD.

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_A_G_B Col_G_H_G nCol_G_H_A) as OppositeSide_A_GH_B.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_A_GH_B) as OppositeSide_B_GH_A.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_D_B_GH OppositeSide_B_GH_A) as OppositeSide_D_GH_A.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_D_GH_A) as OppositeSide_A_GH_D.

	pose proof (proposition_27 _ _ _ _ _ _ BetS_A_G_B BetS_C_H_D CongA_AGH_GHD OppositeSide_A_GH_D) as Par_AB_CD.

	exact Par_AB_CD.
Qed.

End Euclid.
