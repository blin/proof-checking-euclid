Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.proposition_15a.
Require Import ProofCheckingEuclid.proposition_27.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_28A :
	forall A B C D E G H,
	BetS A G B ->
	BetS C H D ->
	BetS E G H ->
	CongA E G B G H D ->
	SameSide B D G H ->
	Par A B C D.
Proof.
	intros A B C D E G H.
	intros BetS_A_G_B.
	intros BetS_C_H_D.
	intros BetS_E_G_H.
	intros CongA_EGB_GHD.
	intros SameSide_B_D_GH.

	assert (eq G G) as eq_G_G by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C G H G eq_G_G) as Col_G_H_G.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_G_B) as BetS_B_G_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_G_B) as (_ & neq_A_G & _).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_G_B) as Col_A_G_B.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_G_H) as Col_E_G_H.
	pose proof (by_prop_Col_order _ _ _ Col_E_G_H) as (_ & _ & _ & _ & Col_H_G_E).

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_EGB_GHD) as CongA_GHD_EGB.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_GHD_EGB) as nCol_E_G_B.
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_E_G_B) as n_Col_E_G_B.

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_B_D_GH) as (SameSide_D_B_GH & _ & _).

	pose proof (proposition_15a _ _ _ _ _ BetS_E_G_H BetS_B_G_A nCol_E_G_B) as CongA_EGB_AGH.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_EGB_AGH) as CongA_AGH_EGB.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_AGH_EGB CongA_EGB_GHD) as CongA_AGH_GHD.

	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_EGB_AGH) as nCol_A_G_H.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_G_H) as (nCol_G_A_H & nCol_G_H_A & nCol_H_A_G & nCol_A_H_G & nCol_H_G_A).

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_A_G_B Col_G_H_G nCol_G_H_A) as OppositeSide_A_GH_B.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_A_GH_B) as OppositeSide_B_GH_A.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_D_B_GH OppositeSide_B_GH_A) as OppositeSide_D_GH_A.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_D_GH_A) as OppositeSide_A_GH_D.

	pose proof (proposition_27 _ _ _ _ _ _ BetS_A_G_B BetS_C_H_D CongA_AGH_GHD OppositeSide_A_GH_D) as Par_AB_CD.

	exact Par_AB_CD.
Qed.

End Euclid.
