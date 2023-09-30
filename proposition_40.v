Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.proposition_31short.
Require Import ProofCheckingEuclid.proposition_38.
Require Import ProofCheckingEuclid.proposition_39.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_40 :
	forall A B C D E H,
	Cong B C H E ->
	EqAreaTri A B C D H E ->
	Triangle A B C ->
	Triangle D H E ->
	Col B C H ->
	Col B C E ->
	SameSide A D B C ->
	neq A D ->
	Par A D B C.
Proof.
	intros A B C D E H.
	intros Cong_B_C_H_E.
	intros EqAreaTri_A_B_C_D_H_E.
	intros Triangle_A_B_C.
	intros Triangle_D_H_E.
	intros Col_B_C_H.
	intros Col_B_C_E.
	intros SameSide_A_D_B_C.
	intros neq_A_D.

	assert (eq E E) as eq_E_E by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C H E E eq_E_E) as Col_H_E_E.

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_B_C_H_E) as Cong_H_E_B_C.
	
	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_A_B_C) as nCol_A_B_C.
	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_D_H_E) as nCol_D_H_E.
	
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).

	pose proof (by_prop_nCol_order _ _ _ nCol_D_H_E) as (nCol_H_D_E & nCol_H_E_D & nCol_E_D_H & nCol_D_E_H & nCol_E_H_D).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_D_H_E) as (neq_D_H & neq_H_E & neq_D_E & neq_H_D & neq_E_H & neq_E_D).
	
	pose proof (by_prop_Col_order _ _ _ Col_B_C_H) as (Col_C_B_H & Col_C_H_B & Col_H_B_C & Col_B_H_C & Col_H_C_B).
	pose proof (by_prop_Col_order _ _ _ Col_B_C_E) as (Col_C_B_E & Col_C_E_B & Col_E_B_C & Col_B_E_C & Col_E_C_B).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_B_H Col_C_B_E neq_C_B) as Col_B_H_E.
	pose proof (by_prop_Col_order _ _ _ Col_B_H_E) as (_ & Col_H_E_B & _ & _ & _).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_C_H Col_B_C_E neq_B_C) as Col_C_H_E.
	pose proof (by_prop_Col_order _ _ _ Col_C_H_E) as (_ & Col_H_E_C & _ & _ & _).

	pose proof (lemma_extension E H E H neq_E_H neq_E_H) as (R & BetS_E_H_R & Cong_H_R_E_H).
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_H_R) as BetS_R_H_E.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_H_R) as (neq_H_R & _ & neq_E_R).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_R_H_E) as (_ & neq_R_H & neq_R_E).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_H_R) as Col_E_H_R.
	pose proof (by_prop_Col_order _ _ _ Col_E_H_R) as (Col_H_E_R & Col_H_R_E & Col_R_E_H & Col_E_R_H & Col_R_H_E).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_H_E_D Col_H_E_R Col_H_E_E neq_R_E) as nCol_R_E_D.

	pose proof (proposition_31short _ _ _ _ BetS_R_H_E nCol_R_E_D) as (P & Q & M & BetS_P_D_Q & CongA_P_D_H_D_H_E & Par_P_Q_R_E & BetS_P_M_E & BetS_D_M_H).

	pose proof (by_def_Col_from_BetS_A_B_C P D Q BetS_P_D_Q) as Col_P_D_Q.
	pose proof (by_prop_Col_order _ _ _ Col_P_D_Q) as (_ & _ & _ & Col_P_Q_D & _).

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_P_Q_R_E Col_R_E_H neq_H_E) as Par_P_Q_H_E.

	pose proof (proposition_38 _ _ _ _ _ _ _ _ Par_P_Q_H_E Col_P_Q_D Col_P_Q_D Cong_H_E_B_C Col_H_E_B Col_H_E_C) as EqAreaTri_D_H_E_D_B_C.
	pose proof (axiom_EqAreaTri_transitive _ _ _ _ _ _ _ _ _ EqAreaTri_A_B_C_D_H_E EqAreaTri_D_H_E_D_B_C) as EqAreaTri_A_B_C_D_B_C.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_H_E_D Col_H_E_B Col_H_E_C neq_B_C) as nCol_B_C_D.
	pose proof (by_prop_nCol_order _ _ _ nCol_B_C_D) as (_ & _ & nCol_D_B_C & _ & _).
	pose proof (by_def_Triangle _ _ _ nCol_D_B_C) as Triangle_D_B_C.

	pose proof (proposition_39 _ _ _ _ Triangle_A_B_C Triangle_D_B_C SameSide_A_D_B_C EqAreaTri_A_B_C_D_B_C neq_A_D) as Par_A_D_B_C.

	exact Par_A_D_B_C.
Qed.

End Euclid.