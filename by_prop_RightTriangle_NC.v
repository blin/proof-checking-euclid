Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Midpoint.
Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_doublereverse.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_eq_symmetric.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_midpointunique.
Require Import ProofCheckingEuclid.lemma_partnotequalwhole.
Require Import ProofCheckingEuclid.lemma_s_congruence_null_segment.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_RightTriangle_NC :
	forall A B C,
	RightTriangle A B C ->
	nCol A B C.
Proof.
	intros A B C.
	intros RightTriangle_ABC.

	destruct RightTriangle_ABC as (D & BetS_A_B_D & Cong_AB_DB & Cong_AC_DC & neq_B_C).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_B_D) as (_ & neq_A_B & neq_A_D).
	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_B_D) as Col_A_B_D.
	pose proof (by_prop_Col_order _ _ _ Col_A_B_D) as (Col_B_A_D & _ & _ & _ & _).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_DB) as (_ & _ & Cong_AB_BD).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AC_DC) as (Cong_CA_CD & _ & Cong_AC_CD).
	pose proof (by_prop_Cong_doublereverse _ _ _ _ Cong_AC_DC) as (Cong_CD_CA & _).

	pose proof (by_def_Midpoint _ _ _ BetS_A_B_D Cong_AB_BD) as Midpoint_A_B_D.

	assert (~ BetS A C D) as nBetS_A_C_D.
	{
		intros BetS_A_C_D.

		pose proof (by_def_Midpoint _ _ _ BetS_A_C_D Cong_AC_CD) as Midpoint_A_C_D.
		pose proof (lemma_midpointunique _ _ _ _ Midpoint_A_B_D Midpoint_A_C_D) as eq_B_C.

		contradict eq_B_C.
		exact neq_B_C.
	}

	assert (~ eq C A) as neq_C_A.
	{
		intros eq_C_A.

		assert (Cong C C D C) as Cong_CC_DC by (setoid_rewrite eq_C_A at 1; exact Cong_AC_DC).
		pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_CC_DC) as Cong_DC_CC.
		pose proof (lemma_s_congruence_null_segment _ _ _ Cong_DC_CC) as eq_D_C.
		assert (eq D A) as eq_D_A by (rewrite <- eq_C_A; exact eq_D_C).
		pose proof (by_prop_eq_symmetric _ _ eq_D_A) as eq_A_D.

		contradict eq_A_D.
		exact neq_A_D.
	}
	pose proof (by_prop_neq_symmetric _ _ neq_C_A) as neq_A_C.

	assert (~ eq C D) as neq_C_D.
	{
		intros eq_C_D.

		assert (Cong A C D D) as Cong_AC_DD by (setoid_rewrite <- eq_C_D at 2; exact Cong_AC_DC).
		pose proof (lemma_s_congruence_null_segment _ _ _ Cong_AC_DD) as eq_A_C.
		pose proof (by_prop_eq_symmetric _ _ eq_A_C) as eq_C_A.

		contradict eq_C_A.
		exact neq_C_A.
	}

	assert (~ BetS C A D) as nBetS_C_A_D.
	{
		intros BetS_C_A_D.

		pose proof (lemma_partnotequalwhole _ _ _ BetS_C_A_D) as nCong_CA_CD.

		contradict Cong_CA_CD.
		exact nCong_CA_CD.
	}

	assert (~ BetS A D C) as nBetS_A_D_C.
	{
		intros BetS_A_D_C.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_C) as BetS_C_D_A.
		pose proof (lemma_partnotequalwhole _ _ _ BetS_C_D_A) as nCong_CD_CA.

		contradict Cong_CD_CA.
		exact nCong_CD_CA.
	}

	assert (nCol A C D) as nCol_A_C_D.
	unfold nCol.
	repeat split.
	exact neq_A_C.
	exact neq_A_D.
	exact neq_C_D.
	exact nBetS_A_C_D.
	exact nBetS_A_D_C.
	exact nBetS_C_A_D.

	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_C_D) as n_Col_A_C_D.

	assert (~ Col A B C) as n_Col_A_B_C.
	{
		intros Col_A_B_C.

		pose proof (by_prop_Col_order _ _ _ Col_A_B_C) as (Col_B_A_C & _ & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_A_C Col_B_A_D neq_B_A) as Col_A_C_D.

		contradict Col_A_C_D.
		exact n_Col_A_C_D.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_A_B_C) as nCol_A_B_C.

	exact nCol_A_B_C.
Qed.

End Euclid.
