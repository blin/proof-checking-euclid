Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_right_triangle.
Require Import ProofCheckingEuclid.proposition_01.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_11_neq_A_C :
	forall A C,
	neq A C ->
	exists X, RightTriangle A C X.
Proof.
	intros A C.
	intros neq_A_C.

	pose proof (lemma_extension _ _ _ _ neq_A_C neq_A_C) as (E & BetS_A_C_E & Cong_CE_AC).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_C_E) as (_ & _ & neq_A_E).
	assert (Col A C E) as Col_A_C_E by (unfold Col; one_of_disjunct BetS_A_C_E).
	pose proof (lemma_collinearorder _ _ _ Col_A_C_E) as (_ & _ & _ & Col_A_E_C & _).

	pose proof (lemma_doublereverse _ _ _ _ Cong_CE_AC) as (Cong_CA_EC & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_CA_EC) as (_ & Cong_AC_EC & _ ).

	pose proof (proposition_01 _ _ neq_A_E) as (F & equilateral_AEF & Triangle_AEF).

	destruct equilateral_AEF as (_ & Cong_EF_FA).
	pose proof (lemma_doublereverse _ _ _ _ Cong_EF_FA) as (Cong_AF_FE & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AF_FE) as (_ & _ & Cong_AF_EF).

	assert (nCol A E F) as nCol_A_E_F by (unfold Triangle in Triangle_AEF; exact Triangle_AEF).
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_E_F) as n_Col_A_E_F.
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_E_F Col_A_E_C neq_A_C) as nCol_A_C_F.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_C_F) as (_ & neq_C_F & _ & _ & _ & _).

	pose proof (lemma_s_right_triangle _ _ _ _ BetS_A_C_E Cong_AC_EC Cong_AF_EF neq_C_F) as RightTriangle_ACF.

	exists F.
	exact RightTriangle_ACF.
Qed.

Lemma proposition_11 :
	forall A B C,
	BetS A C B ->
	exists X, RightTriangle A C X.
Proof.
	intros A B C.
	intros BetS_A_C_B.

	pose proof (lemma_betweennotequal _ _ _ BetS_A_C_B) as (_ & neq_A_C & _).
	pose proof (proposition_11_neq_A_C _ _ neq_A_C) as (F & RightTriangle_ACF).

	exists F.
	exact RightTriangle_ACF.
Qed.

End Euclid.
