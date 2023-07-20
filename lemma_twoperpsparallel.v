Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_SumTwoRT.
Require Import ProofCheckingEuclid.by_def_Supp.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_collinear.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Euclid4.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.proposition_28C.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

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

	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_ABC) as nCol_A_B_C.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (_ & neq_B_C & _ & _ & _ & _).

	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_BCD) as nCol_B_C_D.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_C_D) as (_ & neq_C_D & _ & _ & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_D) as OnRay_CD_D.

	pose proof (postulate_Euclid2 _ _ neq_B_C) as (E & BetS_B_C_E).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_C_E) as (neq_C_E & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_C_E) as neq_E_C.

	pose proof (by_def_Supp _ _ _ _ _ OnRay_CD_D BetS_B_C_E) as Supp_BCD_DCE.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_C_E) as Col_B_C_E.
	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_BCD Col_B_C_E neq_E_C) as RightTriangle_ECD.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_ECD) as RightTriangle_DCE.

	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_BCD RightTriangle_DCE) as CongA_BCD_DCE.

	pose proof (by_def_SumTwoRT _ _ _ _ _ _ _ _ _ _ _ Supp_BCD_DCE CongA_ABC_BCD CongA_BCD_DCE) as SumTwoRT_ABC_BCD.

	pose proof (proposition_28C _ _ _ _ SumTwoRT_ABC_BCD SameSide_A_D_BC) as Par_BA_CD.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_BA_CD) as Par_CD_BA.
	pose proof (by_prop_Par_flip _ _ _ _ Par_CD_BA) as (_ & Par_CD_AB & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_CD_AB) as Par_AB_CD.

	exact Par_AB_CD.
Qed.

End Euclid.

