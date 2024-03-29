Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_distinct.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.proposition_27.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_27B :
	forall A D E F,
	CongA A E F E F D ->
	OppositeSide A E F D ->
	Par A E F D.
Proof.
	intros A D E F.
	intros CongA_AEF_EFD.
	intros OppositeSide_A_EF_D.

	pose proof (by_prop_CongA_distinct _ _ _ _ _ _ CongA_AEF_EFD) as (neq_A_E & _ & _ & _ & _ & _).
	pose proof (by_prop_CongA_distinct _ _ _ _ _ _ CongA_AEF_EFD) as (_ & _ & _ & _ & neq_F_D & _).

	pose proof (by_prop_neq_symmetric _ _ neq_A_E) as neq_E_A.
	pose proof (by_prop_neq_symmetric _ _ neq_F_D) as neq_D_F.

	pose proof (postulate_Euclid2 _ _ neq_A_E) as (B & BetS_A_E_B).
	pose proof (postulate_Euclid2 _ _ neq_D_F) as (C & BetS_D_F_C).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_E_B) as Col_A_E_B.
	pose proof (by_prop_Col_order _ _ _ Col_A_E_B) as (_ & _ & Col_B_A_E & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_F_C) as BetS_C_F_D.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_D_F_C) as Col_D_F_C.
	pose proof (by_prop_Col_order _ _ _ Col_D_F_C) as (_ & _ & Col_C_D_F & _ & _).

	pose proof (proposition_27 _ _ _ _ _ _ BetS_A_E_B BetS_C_F_D CongA_AEF_EFD OppositeSide_A_EF_D) as Par_AB_CD.

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_AB_CD Col_C_D_F neq_F_D) as Par_AB_FD.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AB_FD) as Par_FD_AB.
	pose proof (by_prop_Par_flip _ _ _ _ Par_FD_AB) as (_ & Par_FD_BA & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_FD_BA Col_B_A_E neq_E_A) as Par_FD_EA.
	pose proof (by_prop_Par_flip _ _ _ _ Par_FD_EA) as (_ & Par_FD_AE & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_FD_AE) as Par_AE_FD.

	exact Par_AE_FD.
Qed.

End Euclid.
