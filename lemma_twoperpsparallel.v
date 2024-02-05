Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_SumTwoRT.
Require Import ProofCheckingEuclid.by_def_Supp.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_collinear.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Euclid4.
Require Import ProofCheckingEuclid.proposition_28B.


Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_twoperpsparallel :
	forall A B C D,
	RightTriangle A B C ->
	RightTriangle B C D ->
	SameSide A D B C ->
	Par A B C D.
Proof.
	intros A B C D.
	intros RightTriangle_ABC.
	intros RightTriangle_BCD.
	intros SameSide_A_D_BC.

	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_ABC RightTriangle_BCD) as CongA_ABC_BCD.

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ABC_BCD) as CongA_BCD_ABC.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_ABC_BCD) as nCol_B_C_D.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_BCD_ABC) as nCol_A_B_C.

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_C_D) as (_ & neq_C_D & neq_B_D & _ & neq_D_C & neq_D_B).

	pose proof (by_prop_CongA_reflexive _ _ _ nCol_A_B_C) as CongA_ABC_ABC.

	pose proof (postulate_Euclid2 _ _ neq_A_B) as (E & BetS_A_B_E).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_E) as BetS_E_B_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_B_A) as (_& neq_E_B & neq_E_A).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_B_E) as Col_A_B_E.
	pose proof (by_prop_Col_order _ _ _ Col_A_B_E) as (Col_B_A_E & Col_B_E_A & Col_E_A_B & Col_A_E_B & Col_E_B_A).

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_C) as OnRay_BC_C.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_BC_C BetS_A_B_E) as Supp_ABC_CBE.

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_ABC Col_A_B_E neq_E_B) as RightTriangle_EBC.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_EBC) as RightTriangle_CBE.

	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_BCD RightTriangle_CBE) as CongA_BCD_CBE.

	pose proof (by_def_SumTwoRT _ _ _ _ _ _ _ _ _ _ _ Supp_ABC_CBE CongA_ABC_ABC CongA_BCD_CBE) as SumTwoRT_ABC_BCD.

	pose proof (postulate_Euclid2 _ _ neq_D_C) as (F & BetS_D_C_F).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_C_F) as BetS_F_C_D.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_D_C_F) as Col_D_C_F.
	pose proof (by_prop_Col_order _ _ _ Col_D_C_F) as (Col_C_D_F & Col_C_F_D & Col_F_D_C & Col_D_F_C & Col_F_C_D).

	pose proof (proposition_28B _ _ _ _ _ _ BetS_E_B_A BetS_F_C_D SumTwoRT_ABC_BCD SameSide_A_D_BC) as Par_EA_FD.

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_EA_FD Col_F_D_C neq_C_D) as Par_EA_CD.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_EA_CD) as Par_CD_EA.

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_CD_EA Col_E_A_B neq_B_A) as Par_CD_BA.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_CD_BA) as Par_BA_CD.
	pose proof (by_prop_Par_flip _ _ _ _ Par_BA_CD) as (Par_AB_CD & Par_BA_DC & Par_AB_DC).

	exact Par_AB_CD.
Qed.

End Euclid.
