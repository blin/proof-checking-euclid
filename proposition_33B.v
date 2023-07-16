Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_crisscross.
Require Import ProofCheckingEuclid.lemma_parallelNC.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_samenotopposite.
Require Import ProofCheckingEuclid.proposition_33.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_33B :
	forall A B C D,
	Par A B C D ->
	Cong A B C D ->
	SameSide A C B D ->
	Par A C B D /\ Cong A C B D.
Proof.
	intros A B C D.
	intros Par_AB_CD.
	intros Cong_AB_CD.
	intros SameSide_A_C_BD.

	pose proof (lemma_parallelNC _ _ _ _ Par_AB_CD) as (_ & _ & _ & nCol_A_B_D).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_D) as (_ & nCol_B_D_A & _ & _ & _).

	pose proof (lemma_samenotopposite _ _ _ _ SameSide_A_C_BD) as n_OppositeSide_A_BD_C.

	assert (~ Cross A C B D) as n_CR_A_C_B_D.
	{
		intro CR_A_C_B_D.

		destruct CR_A_C_B_D as (M & BetS_A_M_C & BetS_B_M_D).

		pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_B_M_D) as Col_B_M_D.
		pose proof (lemma_collinearorder _ _ _ Col_B_M_D) as (_ & _ & _ & Col_B_D_M & _).

		pose proof (by_def_OppositeSide _ _ _ _ _ BetS_A_M_C Col_B_D_M nCol_B_D_A) as OppositeSide_A_BD_C.

		contradict OppositeSide_A_BD_C.
		exact n_OppositeSide_A_BD_C.
	}

	pose proof (lemma_crisscross _ _ _ _ Par_AB_CD n_CR_A_C_B_D) as CR_A_D_C_B.

	destruct CR_A_D_C_B as (m & BetS_A_m_D & BetS_C_m_B).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_m_B) as BetS_B_m_C.

	pose proof (proposition_33 _ _ _ _ _ Par_AB_CD Cong_AB_CD BetS_A_m_D BetS_B_m_C) as (Par_AC_BD & Cong_AC_BD).

	split.
	exact Par_AC_BD.
	exact Cong_AC_BD.
Qed.

End Euclid.
