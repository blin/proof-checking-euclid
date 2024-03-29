Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_RightTriangle.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_leg_change.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_droppedperpendicularunique.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_extensionunique.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_RightTriangle_CBA_n_ACB :
	forall A B C,
	RightTriangle C B A ->
	~ RightTriangle A C B.
Proof.
	intros A B C.
	intros RightTriangle_CBA.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_CBA) as RightTriangle_ABC.

	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_CBA) as nCol_C_B_A.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_C_B_A) as (neq_C_B & neq_B_A & neq_C_A & neq_B_C & neq_A_B & neq_A_C).

	pose proof (lemma_extension _ _ _ _ neq_B_C neq_C_B) as (E & BetS_B_C_E & Cong_CE_CB).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_C_E) as BetS_E_C_B.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_C_E) as Col_B_C_E.
	pose proof (by_prop_Col_order _ _ _ Col_B_C_E) as (_ & _ & _ & _ & Col_E_C_B).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_CE_CB) as (_ & _ & Cong_CE_BC).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_CE_BC) as Cong_BC_CE.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_CE_CB) as (Cong_EC_BC & _ & _).

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_C_E neq_B_C) as OnRay_BC_E.
	pose proof (by_prop_RightTriangle_leg_change _ _ _ _ RightTriangle_ABC OnRay_BC_E) as RightTriangle_ABE.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_ABE) as RightTriangle_EBA.

	assert (~ RightTriangle A C B) as n_RightTriangle_ACB.
	{
		intro RightTriangle_ACB.

		pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_ACB) as RightTriangle_BCA.

		destruct RightTriangle_BCA as (F & BetS_B_C_F & Cong_BC_FC & Cong_BA_FA & _).

		pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BC_FC) as Cong_FC_BC.
		pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BA_FA) as Cong_FA_BA.

		pose proof (by_prop_Cong_flip _ _ _ _ Cong_FC_BC) as (_ & Cong_CF_BC & _).
		pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_CF_BC Cong_BC_CE) as Cong_CF_CE.

		pose proof (lemma_extensionunique _ _ _ _ BetS_B_C_F BetS_B_C_E Cong_CF_CE) as eq_F_E.

		assert (Cong E A B A) as Cong_EA_BA by (rewrite <- eq_F_E; exact Cong_FA_BA).

		pose proof (by_def_RightTriangle _ _ _ _ BetS_E_C_B Cong_EC_BC Cong_EA_BA neq_C_A) as RightTriangle_ECA.

		pose proof (lemma_droppedperpendicularunique _ _ _ _ RightTriangle_ECA RightTriangle_EBA Col_E_C_B) as eq_C_B.

		contradict eq_C_B.
		exact neq_C_B.
	}

	exact n_RightTriangle_ACB.
Qed.

End Euclid.
