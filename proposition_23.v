Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_TogetherGreater_flip.
Require Import ProofCheckingEuclid.by_prop_TogetherGreater_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.proposition_20.
Require Import ProofCheckingEuclid.proposition_22.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_23 :
	forall A B C D E,
	neq A B ->
	nCol D C E ->
	exists X Y, OnRay A B Y /\ CongA X A Y D C E.
Proof.
	intros A B C D E.
	intros neq_A_B.
	intros nCol_D_C_E.

	pose proof (by_prop_nCol_order _ _ _ nCol_D_C_E) as (_ & nCol_C_E_D & _ & _ & nCol_E_C_D).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_D_C_E) as (_ & neq_C_E & _ & neq_C_D & _ & _).

	pose proof (by_def_Triangle _ _ _ nCol_D_C_E) as Triangle_DCE.
	pose proof (by_def_Triangle _ _ _ nCol_C_E_D) as Triangle_CED.
	pose proof (by_def_Triangle _ _ _ nCol_E_C_D) as Triangle_ECD.
	pose proof (proposition_20 _ _ _ Triangle_DCE) as TogetherGreater_CD_DE_CE.
	pose proof (proposition_20 _ _ _ Triangle_ECD) as TogetherGreater_CE_ED_CD.
	pose proof (proposition_20 _ _ _ Triangle_CED) as TogetherGreater_EC_CD_ED.

	pose proof (by_prop_TogetherGreater_symmetric _ _ _ _ _ _ TogetherGreater_EC_CD_ED) as TogetherGreater_CD_EC_ED.
	pose proof (by_prop_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_CD_DE_CE) as (_ & TogetherGreater_CD_DE_EC).
	pose proof (by_prop_TogetherGreater_symmetric _ _ _ _ _ _ TogetherGreater_CD_DE_EC) as TogetherGreater_DE_CD_EC.
	pose proof (by_prop_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_DE_CD_EC) as (TogetherGreater_ED_CD_EC & _).
	pose proof (by_prop_TogetherGreater_symmetric _ _ _ _ _ _ TogetherGreater_ED_CD_EC) as TogetherGreater_CD_ED_EC.
	pose proof (by_prop_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_CE_ED_CD) as (TogetherGreater_EC_ED_CD & _).

	pose proof (proposition_22 _ _ _ _ _ _ _ _ TogetherGreater_CD_EC_ED TogetherGreater_CD_ED_EC TogetherGreater_EC_ED_CD neq_A_B) as (G & F & Cong_AG_EC & Cong_AF_CD & Cong_GF_ED & OnRay_AB_G & Triangle_AGF).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AG_EC) as (_ & _ & Cong_AG_CE).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_GF_ED) as (Cong_FG_DE & _ & _).

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_AGF) as nCol_A_G_F.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_G_F) as (neq_A_G & _ & neq_A_F & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_G_F) as (_ & _ & nCol_F_A_G & _ & _).

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_A_F) as OnRay_AF_F.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_A_G) as OnRay_AG_G.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_D) as OnRay_CD_D.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_E) as OnRay_CE_E.

	pose proof (by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_AF_F OnRay_AG_G OnRay_CD_D OnRay_CE_E Cong_AF_CD Cong_AG_CE Cong_FG_DE nCol_F_A_G) as CongA_FAG_DCE.

	exists F,G.
	split.
	exact OnRay_AB_G.
	exact CongA_FAG_DCE.
Qed.

End Euclid.
