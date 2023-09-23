Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_planeseparation.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_parallelPasch :
	forall A B C D E,
	Parallelogram A B C D ->
	BetS A D E ->
	exists X, BetS B X E /\ BetS C X D.
Proof.
	intros A B C D E.
	intros Parallelogram_A_B_C_D.
	intros BetS_A_D_E.

	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq D D) as eq_D_D by (reflexivity).
	pose proof (by_def_Col_from_eq_A_B C C B eq_C_C) as Col_C_C_B.
	pose proof (by_def_Col_from_eq_B_C A D D eq_D_D) as Col_A_D_D.
	pose proof (by_def_Col_from_eq_B_C C D D eq_D_D) as Col_C_D_D.

	assert (Parallelogram_A_B_C_D_2 := Parallelogram_A_B_C_D).
	destruct Parallelogram_A_B_C_D_2 as (Par_AB_CD & Par_AD_BC).

	assert (Par_AD_BC_2 := Par_AD_BC).
	destruct Par_AD_BC_2 as (_ & _ & _ & _ & _ & neq_A_D & neq_B_C & _ & _ & _ & _ & _ & _ & n_Meet_A_D_B_C & _ & _).

	pose proof (by_prop_neq_symmetric _ _ neq_A_D) as neq_D_A.
	pose proof (by_prop_neq_symmetric _ _ neq_B_C) as neq_C_B.

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AB_CD) as Par_CD_AB.
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_CD_AB) as TarskiPar_CD_AB.
	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (_ & nCol_A_C_D & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_C_D) as (_ & nCol_C_D_A & _ & _ & _).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_D_E) as (neq_D_E & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_D_E) as neq_E_D.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_D_E) as Col_A_D_E.
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_D_D Col_A_D_E neq_A_D) as Col_D_D_E.
	pose proof (by_prop_Col_order _ _ _ Col_D_D_E) as (_ & _ & Col_E_D_D & _ & _).

	assert (TarskiPar_CD_AB_2 := TarskiPar_CD_AB).
	destruct TarskiPar_CD_AB_2 as (neq_C_D & neq_A_B & n_Meet_C_D_A_B & SameSide_A_B_CD).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_A_B_CD) as (SameSide_B_A_CD & _ & _).
	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_A_D_E Col_C_D_D nCol_C_D_A) as OppositeSide_A_CD_E.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_B_A_CD OppositeSide_A_CD_E) as OppositeSide_B_CD_E.

	destruct OppositeSide_B_CD_E as (H & BetS_B_H_E & Col_C_D_H & nCol_C_D_B).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_H_E) as BetS_E_H_B.

	pose proof (by_prop_Col_order _ _ _ Col_C_D_H) as (Col_D_C_H & _ & _ & _ & _).

	assert (~ Meet E D C B) as n_Meet_E_D_C_B.
	{
		intro Meet_E_D_C_B.

		destruct Meet_E_D_C_B as (p & _ & _ & Col_E_D_p & Col_C_B_p).

		pose proof (by_prop_Col_order _ _ _ Col_C_B_p) as (Col_B_C_p & _ & _ & _ & _).
		pose proof (by_prop_Col_order _ _ _ Col_A_D_E) as (_ & _ & _ & _ & Col_E_D_A).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_E_D_A Col_E_D_p neq_E_D) as Col_D_A_p.
		pose proof (by_prop_Col_order _ _ _ Col_D_A_p) as (Col_A_D_p & _ & _ & _ & _).

		pose proof (by_def_Meet _ _ _ _ _ neq_A_D neq_B_C Col_A_D_p Col_B_C_p) as Meet_A_D_B_C.

		contradict Meet_A_D_B_C.
		exact n_Meet_A_D_B_C.
	}

	pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_E_D_D Col_C_C_B neq_E_D neq_C_B neq_E_D neq_C_B n_Meet_E_D_C_B BetS_E_H_B Col_D_C_H) as BetS_D_H_C.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_H_C) as BetS_C_H_D.

	exists H.
	split.
	exact BetS_B_H_E.
	exact BetS_C_H_D.
Qed.

End Euclid.
