Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Midpoint.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_RightTriangle.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_collinear.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_reverse.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennesspreserved.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_notperp.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_pointreflectionisometry.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.proposition_10.
Require Import ProofCheckingEuclid.proposition_12.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_11B :
	forall A B C P,
	BetS A C B ->
	nCol A B P ->
	exists X, RightTriangle A C X /\ OppositeSide X A B P.
Proof.
	intros A B C P.
	intros BetS_A_C_B.
	intros nCol_A_B_P.

	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C A B A eq_A_A) as Col_A_B_A.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_C_B) as (_ & _ & neq_A_B).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_C_B) as (_ & neq_A_C & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_C_B) as (neq_C_B & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_neq_symmetric _ _ neq_A_C) as neq_C_A.

	pose proof (by_def_Col_from_BetS_A_C_B _ _ _ BetS_A_C_B) as Col_A_B_C.
	pose proof (by_prop_Col_order _ _ _ Col_A_B_C) as (Col_B_A_C & Col_B_C_A & Col_C_A_B & Col_A_C_B & Col_C_B_A).

	pose proof (lemma_notperp _ _ _ _ BetS_A_C_B nCol_A_B_P) as (M & nCol_A_B_M & SameSide_M_P_AB & n_RightTriangle_ACM).

	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_M) as n_Col_A_B_M.

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_M_P_AB) as (SameSide_P_M_AB & _ & _).

	pose proof (proposition_12 _ _ _ nCol_A_B_M) as (Q & Perp_at_M_Q_A_B_Q).
	destruct Perp_at_M_Q_A_B_Q as (E & _ & Col_A_B_Q & Col_A_B_E & RightTriangle_EQM).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_B_Q Col_A_B_C neq_A_B) as Col_B_Q_C.
	pose proof (by_prop_Col_order _ _ _ Col_B_Q_C) as (_ & Col_Q_C_B & _ & _ & _).

	pose proof (by_prop_Col_order _ _ _ Col_A_B_E) as (Col_B_A_E & _ & _ & _ & _).
	pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_A_B Col_A_B_C Col_A_B_Q Col_A_B_E) as Col_C_Q_E.
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_A_E Col_B_A_C neq_B_A) as Col_A_E_C.
	pose proof (by_prop_Col_order _ _ _ Col_A_E_C) as (_ & Col_E_C_A & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_C_Q_E) as (_ & _ & _ & _ & Col_E_Q_C).

	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_EQM) as nCol_E_Q_M.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_E_Q_M) as (neq_E_Q & neq_Q_M & neq_E_M & neq_Q_E & neq_M_Q & neq_M_E).


	assert (~ eq C Q) as n_eq_C_Q.
	{
		intro eq_C_Q.

		assert (RightTriangle E C M) as RightTriangle_ECM by (rewrite eq_C_Q; exact RightTriangle_EQM).
		pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_ECM Col_E_C_A neq_A_C) as RightTriangle_ACM.

		contradict RightTriangle_ACM.
		exact n_RightTriangle_ACM.
	}
	assert (neq_C_Q := n_eq_C_Q).

	pose proof (by_prop_neq_symmetric _ _ neq_C_Q) as neq_Q_C.

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_EQM Col_E_Q_C neq_C_Q) as RightTriangle_CQM.
	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_CQM) as nCol_C_Q_M.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_C_Q_M) as (_ & _ & neq_C_M & _ & _ & neq_M_C).
	pose proof (by_prop_nCol_order _ _ _ nCol_C_Q_M) as (nCol_Q_C_M & nCol_Q_M_C & nCol_M_C_Q & nCol_C_M_Q & nCol_M_Q_C).

	pose proof (proposition_10 _ _ neq_Q_C) as (G & BetS_Q_G_C & Cong_GQ_GC).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_Q_G_C) as (_ & neq_Q_G & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_Q_G_C) as (neq_G_C & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_Q_G) as neq_G_Q.
	pose proof (by_prop_neq_symmetric _ _ neq_G_C) as neq_C_G.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_Q_G_C) as Col_Q_G_C.
	pose proof (by_prop_Col_order _ _ _ Col_Q_G_C) as (Col_G_Q_C & Col_G_C_Q & Col_C_Q_G & Col_Q_C_G & Col_C_G_Q).

	pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_A_B Col_A_B_Q Col_A_B_C Col_A_B_A) as Col_Q_C_A.
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_Q_C_A Col_Q_C_G neq_Q_C) as Col_C_A_G.
	pose proof (by_prop_Col_order _ _ _ Col_C_A_G) as (_ & _ & Col_G_C_A & _ & _).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_A_G Col_C_A_B neq_C_A) as Col_A_G_B.
	pose proof (by_prop_Col_order _ _ _ Col_A_G_B) as (_ & _ & _ & Col_A_B_G & _).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_GQ_GC) as (_ & Cong_QG_GC & _).
	pose proof (by_def_Midpoint _ _ _ BetS_Q_G_C Cong_QG_GC) as Midpoint_Q_G_C.

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_CQM Col_C_Q_G neq_G_Q) as RightTriangle_GQM.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_GQM) as RightTriangle_MQG.

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_Q_C_M Col_Q_C_G neq_Q_G) as nCol_Q_G_M.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_Q_G_M) as (_ & neq_G_M & _ & _ & neq_M_G & _).

	pose proof (lemma_extension _ _ _ _ neq_M_Q neq_M_Q) as (J & BetS_M_Q_J & Cong_QJ_MQ).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_M_Q_J) as BetS_J_Q_M.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_J_Q_M) as (_ & neq_J_Q & _).
	pose proof (by_prop_neq_symmetric _ _ neq_J_Q) as neq_Q_J.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_M_Q_J) as (_ & _ & neq_M_J).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_QJ_MQ) as Cong_MQ_QJ.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_QJ_MQ) as (_ & Cong_JQ_MQ & _).

	pose proof (by_prop_RightTriangle_reverse _ _ _ _ RightTriangle_MQG BetS_M_Q_J Cong_MQ_QJ) as Cong_MG_JG.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_MG_JG) as Cong_JG_MG.
	pose proof (by_def_RightTriangle _ _ _ _ BetS_J_Q_M Cong_JQ_MQ Cong_JG_MG neq_Q_G) as RightTriangle_JQG.
	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_JQG) as nCol_J_Q_G.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_J_Q_G) as (_ & _ & neq_J_G & _ & _ & neq_G_J).

	pose proof (lemma_extension _ _ _ _ neq_J_G neq_J_G) as (K & BetS_J_G_K & Cong_GK_JG).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_GK_JG) as Cong_JG_GK.
	pose proof (by_def_Midpoint _ _ _ BetS_J_G_K Cong_JG_GK) as Midpoint_J_G_K.

	pose proof (lemma_extension _ _ _ _ neq_M_G neq_M_G) as (H & BetS_M_G_H & Cong_GH_MG).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_GH_MG) as Cong_MG_GH.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_GH_MG) as (Cong_HG_GM & _ & _).

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_M_G_H Col_A_B_G nCol_A_B_M) as OppositeSide_M_AB_H.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_P_M_AB OppositeSide_M_AB_H) as OppositeSide_P_AB_H.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_P_AB_H) as OppositeSide_H_AB_P.

	pose proof (by_def_Midpoint _ _ _ BetS_M_G_H Cong_MG_GH) as Midpoint_M_G_H.

	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_M_G_H Midpoint_Q_G_C neq_M_Q) as Cong_MQ_HC.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_Q_G_C Midpoint_J_G_K neq_Q_J) as Cong_QJ_CK.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_M_G_H Midpoint_J_G_K neq_M_J) as Cong_MJ_HK.

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_MQ_HC) as Cong_HC_MQ.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_MG_JG) as (_ & Cong_GM_JG & _).
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_HG_GM Cong_GM_JG) as Cong_HG_JG.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_HG_JG Cong_JG_GK) as Cong_HG_GK.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_HG_GK) as (_ & _ & Cong_HG_KG).
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_HC_MQ Cong_MQ_QJ) as Cong_HC_QJ.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_HC_QJ Cong_QJ_CK) as Cong_HC_CK.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_HC_CK) as (_ & _ & Cong_HC_KC).

	pose proof (lemma_betweennesspreserved _ _ _ _ _ _ Cong_MQ_HC Cong_MJ_HK Cong_QJ_CK BetS_M_Q_J) as BetS_H_C_K.

	pose proof (by_def_RightTriangle _ _ _ _ BetS_H_C_K Cong_HC_KC Cong_HG_KG neq_C_G) as RightTriangle_HCG.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_HCG) as RightTriangle_GCH.
	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_GCH Col_G_C_A neq_A_C) as RightTriangle_ACH.

	exists H.
	split.
	exact RightTriangle_ACH.
	exact OppositeSide_H_AB_P.
Qed.

End Euclid.
