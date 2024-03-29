Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_SameSide.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.proposition_23B.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_23C :
	forall A B C D E P,
	neq A B ->
	nCol D C E ->
	nCol A B P ->
	exists X Y, OnRay A B Y /\ CongA X A Y D C E /\ SameSide X P A B.
Proof.
	intros A B C D E P.
	intros neq_A_B.
	intros nCol_D_C_E.
	intros nCol_A_B_P.

	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C A B A eq_A_A) as Col_A_B_A.

	pose proof (by_prop_nCol_distinct _ _ _ nCol_D_C_E) as (neq_D_C & neq_C_E & neq_D_E & neq_C_D & neq_E_C & neq_E_D).
	pose proof (by_prop_nCol_order _ _ _ nCol_D_C_E) as (nCol_C_D_E & nCol_C_E_D & nCol_E_D_C & nCol_D_E_C & nCol_E_C_D).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_P) as (_ & neq_B_P & neq_A_P & neq_B_A & neq_P_B & neq_P_A).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_P) as (nCol_B_A_P & nCol_B_P_A & nCol_P_A_B & nCol_A_P_B & nCol_P_B_A).


	pose proof (postulate_Euclid2 _ _ neq_P_A) as (Q & BetS_P_A_Q).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_P_A_Q) as (neq_A_Q & _ & neq_P_Q).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_P_A_Q) as Col_P_A_Q.
	pose proof (by_prop_Col_order _ _ _ Col_P_A_Q) as (Col_A_P_Q & Col_A_Q_P & Col_Q_P_A & Col_P_Q_A & Col_Q_A_P).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_P_B Col_A_P_Q neq_A_Q) as nCol_A_Q_B.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_Q_B) as (_ & neq_Q_B & _ & neq_Q_A & neq_B_Q & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_Q_B) as (nCol_Q_A_B & nCol_Q_B_A & nCol_B_A_Q & nCol_A_B_Q & nCol_B_Q_A).

	pose proof (proposition_23B _ _ _ _ _ _ neq_A_B nCol_D_C_E nCol_A_B_Q) as (F & G & OnRay_AB_G & CongA_FAG_DCE & OppositeSide_F_AB_Q).

	destruct OppositeSide_F_AB_Q as (J & BetS_F_J_Q & Col_A_B_J & nCol_A_B_F).

	pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_A_B_J Col_A_B_A BetS_F_J_Q BetS_P_A_Q nCol_A_B_F nCol_A_B_P) as SameSide_F_P_AB.

	exists F, G.
	split.
	exact OnRay_AB_G.
	split.
	exact CongA_FAG_DCE.
	exact SameSide_F_P_AB.
Qed.

End Euclid.
