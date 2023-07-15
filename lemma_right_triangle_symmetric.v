Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_right_triangle_NC.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.by_def_RightTriangle.
Require Import ProofCheckingEuclid.by_def_Supp.
Require Import ProofCheckingEuclid.lemma_supplements_conga.
Require Import ProofCheckingEuclid.proposition_04.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_right_triangle_symmetric :
	forall A B C,
	RightTriangle A B C ->
	RightTriangle C B A.
Proof.
	intros A B C.
	intros RightTriangle_ABC.

	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_ABC) as nCol_A_B_C.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_B_C) as CongA_ABC_CBA.

	destruct RightTriangle_ABC as (D & BetS_A_B_D & Cong_AB_DB & Cong_AC_DC & neq_B_C).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_D) as (_ & neq_A_B & _).

	pose proof (lemma_inequalitysymmetric _ _ neq_B_C) as neq_C_B.
	pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.

	pose proof (lemma_s_onray_assert_ABB _ _ neq_B_A) as OnRay_BA_A.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_B_C) as OnRay_BC_C.

	pose proof (lemma_doublereverse _ _ _ _ Cong_AB_DB) as (Cong_BD_BA & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AC_DC) as (_ & _ & Cong_AC_CD).

	pose proof (lemma_extension _ _ _ _ neq_C_B neq_B_C) as (E & BetS_C_B_E & Cong_BE_BC).

	pose proof (lemma_betweennotequal _ _ _ BetS_C_B_E) as (neq_B_E & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_B_E) as neq_E_B.

	assert (Col C B E) as Col_C_B_E by (unfold Col; one_of_disjunct BetS_C_B_E).
	pose proof (lemma_collinearorder _ _ _ Col_C_B_E) as (_ & _ & _ & _ & Col_E_B_C).

	pose proof (by_def_Supp _ _ _ _ _ OnRay_BC_C BetS_A_B_D) as Supp_ABC_CBD.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_BA_A BetS_C_B_E) as Supp_CBA_ABE.
	pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_ABC_CBA Supp_ABC_CBD Supp_CBA_ABE) as CongA_CBD_ABE.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BE_BC) as Cong_BC_BE.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_BC_BE) as (Cong_CB_EB & _ & _).

	assert (~ Col E B A) as n_Col_E_B_A.
	{
		intros Col_E_B_A.

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_B_A Col_E_B_C neq_E_B) as Col_B_A_C.
		pose proof (lemma_collinearorder _ _ _ Col_B_A_C) as (Col_A_B_C & _ & _ & _ & _).

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_E_B_A) as nCol_E_B_A.
	pose proof (lemma_NCorder _ _ _ nCol_E_B_A) as (_ & _ & _ & _ & nCol_A_B_E).

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_B_E) as CongA_ABE_EBA.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_CBD_ABE CongA_ABE_EBA) as CongA_CBD_EBA.
	pose proof (proposition_04 _ _ _ _ _ _ Cong_BC_BE Cong_BD_BA CongA_CBD_EBA) as (Cong_CD_EA & _ & _).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_AC_CD Cong_CD_EA) as Cong_AC_EA.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AC_EA) as (_ & Cong_CA_EA & _).

	pose proof (by_def_RightTriangle _ _ _ _ BetS_C_B_E Cong_CB_EB Cong_CA_EA neq_B_A) as RightTriangle_CBA.

	exact RightTriangle_CBA.
Qed.

End Euclid.
