Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col .
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Par_NC .
Require Import ProofCheckingEuclid.by_prop_nCol_order .
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_diagonalsbisect.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_trapezoiddiagonals :
	forall A B C D E,
	Parallelogram A B C D ->
	BetS A E D ->
	exists X, BetS B X D /\ BetS C X E.
Proof.
	intros A B C D E.
	intros Parallelogram_A_B_C_D.
	intros BetS_A_E_D.

	assert (eq B B) as eq_B_B by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C A B B eq_B_B) as Col_A_B_B.

	assert (Parallelogram_A_B_C_D_2 := Parallelogram_A_B_C_D).
	destruct Parallelogram_A_B_C_D_2 as (Par_AB_CD & Par_AD_BC).

	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (nCol_A_B_C & nCol_A_C_D & nCol_B_C_D & nCol_A_B_D).
	pose proof (by_prop_nCol_order _ _ _ nCol_B_C_D) as (nCol_C_B_D & nCol_C_D_B & nCol_D_B_C & nCol_B_D_C & nCol_D_C_B).

	assert (Par_AB_CD_2 := Par_AB_CD).
	destruct Par_AB_CD_2 as (_ & _ & _ & _ & _ & neq_A_B & neq_C_D & _ & _ & _ & _ & _ & _ & n_Meet_A_B_C_D & _ & _).

	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_neq_symmetric _ _ neq_C_D) as neq_D_C.

	pose proof (lemma_diagonalsbisect _ _ _ _ Parallelogram_A_B_C_D) as (M & Midpoint_A_M_C & Midpoint_B_M_D).

	assert (Midpoint_A_M_C_2 := Midpoint_A_M_C).
	destruct Midpoint_A_M_C_2 as (BetS_A_M_C & Cong_AM_MC).

	assert (Midpoint_B_M_D_2 := Midpoint_B_M_D).
	destruct Midpoint_B_M_D_2 as (BetS_B_M_D & Cong_BM_MD).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BM_MD) as (_ & _ & Cong_BM_DM).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AM_MC) as (_ & Cong_MA_MC & _).

	pose proof (postulate_Euclid5 _ _ _ _ _ _ BetS_A_M_C BetS_B_M_D BetS_A_E_D Cong_BM_DM Cong_MA_MC nCol_B_D_C) as (P & BetS_B_E_P & BetS_C_D_P).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_D_P) as BetS_P_D_C.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_D_P) as (neq_D_P & _ & neq_C_P).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_P_D_C) as (_ & neq_P_D & neq_P_C).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_D_P) as Col_C_D_P.
	pose proof (by_prop_Col_order _ _ _ Col_C_D_P) as (Col_D_C_P & Col_D_P_C & Col_P_C_D & Col_C_P_D & Col_P_D_C).

	assert (~ Col B P C) as n_Col_B_P_C.
	{
		intro Col_B_P_C.

		pose proof (by_prop_Col_order _ _ _ Col_B_P_C) as (_ & Col_P_C_B & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_P_C_B Col_P_C_D neq_P_C) as Col_C_B_D.
		pose proof (by_prop_Col_order _ _ _ Col_C_B_D) as (_ & _ & _ & Col_C_D_B & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_B Col_C_D_B) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_B_P_C) as nCol_B_P_C.

	pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_B_E_P BetS_C_D_P nCol_B_P_C) as (H' & BetS_B_H'_D & BetS_C_H'_E).

	exists H'.
	split.
	exact BetS_B_H'_D.
	exact BetS_C_H'_E.
Qed.

End Euclid.
