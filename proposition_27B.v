Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_collinearparallel.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_parallelflip.
Require Import ProofCheckingEuclid.lemma_parallelsymmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.proposition_27.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_27B :
	forall A D E F,
	CongA A E F E F D ->
	OS A E F D ->
	Par A E F D.
Proof.
	intros A D E F.
	intros CongA_A_E_F_E_F_D.
	intros OS_A_E_F_D.

	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_A_E_F_E_F_D) as (neq_A_E & _ & _ & _ & _ & _).
	pose proof (lemma_extension A E A E neq_A_E neq_A_E) as (B & BetS_A_E_B & Cong_E_B_A_E).
	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_A_E_F_E_F_D) as (_ & _ & _ & _ & neq_F_D & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_F_D) as neq_D_F.
	pose proof (lemma_extension D F F D neq_D_F neq_F_D) as (C & BetS_D_F_C & Cong_F_C_F_D).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_F_C) as BetS_C_F_D.
	pose proof (proposition_27 _ _ _ _ _ _ BetS_A_E_B BetS_C_F_D CongA_A_E_F_E_F_D OS_A_E_F_D) as Par_A_B_C_D.
	pose proof (lemma_s_col_BetS_A_B_C D F C BetS_D_F_C) as Col_D_F_C.
	pose proof (lemma_collinearorder _ _ _ Col_D_F_C) as (_ & _ & Col_C_D_F & _ & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_A_B_C_D Col_C_D_F neq_F_D) as Par_A_B_F_D.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_A_B_F_D) as Par_F_D_A_B.
	pose proof (lemma_parallelflip _ _ _ _ Par_F_D_A_B) as (_ & Par_F_D_B_A & _).
	pose proof (lemma_s_col_BetS_A_B_C A E B BetS_A_E_B) as Col_A_E_B.
	pose proof (lemma_collinearorder _ _ _ Col_A_E_B) as (_ & _ & Col_B_A_E & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_E) as neq_E_A.
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_F_D_B_A Col_B_A_E neq_E_A) as Par_F_D_E_A.
	pose proof (lemma_parallelflip _ _ _ _ Par_F_D_E_A) as (_ & Par_F_D_A_E & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_F_D_A_E) as Par_A_E_F_D.

	exact Par_A_E_F_D.
Qed.

End Euclid.

