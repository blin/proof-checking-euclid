Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_parallelbetween :
	forall B H K L M,
	BetS H B K ->
	Par M B H L ->
	Col L M K ->
	BetS L M K.
Proof.
	intros B H K L M.
	intros BetS_H_B_K.
	intros Par_M_B_H_L.
	intros Col_L_M_K.
	
	pose proof (by_def_Col_from_BetS_A_B_C H B K BetS_H_B_K) as Col_H_B_K.

	pose proof (by_prop_Par_NC _ _ _ _ Par_M_B_H_L) as (nCol_M_B_H & nCol_M_H_L & nCol_B_H_L & nCol_M_B_L).
	
	assert (Par_M_B_H_L_2 := Par_M_B_H_L).
	destruct Par_M_B_H_L_2 as (_ & _ & _ & _ & _ & neq_M_B & neq_H_L & _ & _ & _ & _ & _ & _ & n_Meet_M_B_H_L & _ & _).
	
	pose proof (by_prop_Col_order _ _ _ Col_L_M_K) as (Col_M_L_K & _ & _ & _ & _).

	pose proof (by_prop_nCol_order _ _ _ nCol_M_H_L) as (_ & _ & _ & nCol_M_L_H & _).

	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq H H) as eq_H_H by (reflexivity).
	assert (eq L L) as eq_L_L by (reflexivity).
	assert (eq M M) as eq_M_M by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C H L H eq_H_H) as Col_H_L_H.
	pose proof (by_def_Col_from_eq_A_C M B M eq_M_M) as Col_M_B_M.
	pose proof (by_def_Col_from_eq_A_C M L M eq_M_M) as Col_M_L_M.
	pose proof (by_def_Col_from_eq_B_C H L L eq_L_L) as Col_H_L_L.
	pose proof (by_def_Col_from_eq_B_C M B B eq_B_B) as Col_M_B_B.

	assert (~ eq M K) as n_eq_M_K.
	{
		intro eq_M_K.

		assert (Col H B M) as Col_H_B_M by (rewrite eq_M_K; exact Col_H_B_K).
		pose proof (by_prop_Col_order _ _ _ Col_H_B_M) as (_ & _ & _ & _ & Col_M_B_H).
		pose proof (by_def_Meet _ _ _ _ _ neq_M_B neq_H_L Col_M_B_H Col_H_L_H) as Meet_M_B_H_L.

		contradict Meet_M_B_H_L.
		exact n_Meet_M_B_H_L.
	}
	assert (neq_M_K := n_eq_M_K).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_M_L_H Col_M_L_M Col_M_L_K neq_M_K) as nCol_M_K_H.
	pose proof (by_prop_nCol_order _ _ _ nCol_M_K_H) as (_ & _ & nCol_H_M_K & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_H_M_K) as (_ & _ & _ & nCol_H_K_M & _).

	(* assert by cases *)
	assert (BetS L M K) as BetS_L_M_K.
	assert (Col_L_M_K_2 := Col_L_M_K).
	destruct Col_L_M_K_2 as [eq_L_M | [eq_L_K | [eq_M_K | [BetS_M_L_K | [BetS_L_M_K | BetS_L_K_M]]]]].
	{
		(* case eq_L_M *)
		assert (Col H L M) as Col_H_L_M by (rewrite <- eq_L_M; exact Col_H_L_L).

		pose proof (by_def_Meet _ _ _ _ _ neq_M_B neq_H_L Col_M_B_M Col_H_L_M) as Meet_M_B_H_L.

		contradict Meet_M_B_H_L.
		exact n_Meet_M_B_H_L.
	}
	{
		(* case eq_L_K *)
		assert (Col H B L) as Col_H_B_L by (rewrite eq_L_K; exact Col_H_B_K).
		pose proof (by_prop_Col_order _ _ _ Col_H_B_L) as (_ & _ & _ & Col_H_L_B & _).

		pose proof (by_def_Meet _ _ _ _ _ neq_M_B neq_H_L Col_M_B_B Col_H_L_B) as Meet_M_B_H_L.

		contradict Meet_M_B_H_L.
		exact n_Meet_M_B_H_L.
	}
	{
		(* case eq_M_K *)
		contradict eq_M_K.
		exact neq_M_K.
	}
	{
		(* case BetS_M_L_K *)
		pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_H_B_K BetS_M_L_K nCol_H_K_M) as (E & BetS_H_E_L & BetS_M_E_B).

		pose proof (by_def_Col_from_BetS_A_B_C H E L BetS_H_E_L) as Col_H_E_L.
		pose proof (by_def_Col_from_BetS_A_B_C M E B BetS_M_E_B) as Col_M_E_B.
		pose proof (by_prop_Col_order _ _ _ Col_H_E_L) as (_ & _ & _ & Col_H_L_E & _).
		pose proof (by_prop_Col_order _ _ _ Col_M_E_B) as (_ & _ & _ & Col_M_B_E & _).

		pose proof (by_def_Meet _ _ _ _ _ neq_M_B neq_H_L Col_M_B_E Col_H_L_E) as Meet_M_B_H_L.

		contradict Meet_M_B_H_L.
		exact n_Meet_M_B_H_L.
	}
	{
		(* case BetS_L_M_K *)
		exact BetS_L_M_K.
	}
	{
		(* case BetS_L_K_M *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_L_K_M) as BetS_M_K_L.
		pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_H_B_K BetS_M_K_L nCol_M_L_H) as (E & BetS_H_E_L & BetS_M_B_E).

		pose proof (by_def_Col_from_BetS_A_B_C H E L BetS_H_E_L) as Col_H_E_L.
		pose proof (by_def_Col_from_BetS_A_B_C M B E BetS_M_B_E) as Col_M_B_E.
		pose proof (by_prop_Col_order _ _ _ Col_H_E_L) as (_ & _ & _ & Col_H_L_E & _).

		pose proof (by_def_Meet _ _ _ _ _ neq_M_B neq_H_L Col_M_B_E Col_H_L_E) as Meet_M_B_H_L.

		contradict Meet_M_B_H_L.
		exact n_Meet_M_B_H_L.
	}

	exact BetS_L_M_K.
Qed.

End Euclid.
