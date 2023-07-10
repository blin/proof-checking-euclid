Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Euclid4.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearright.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_parallelflip.
Require Import ProofCheckingEuclid.lemma_parallelsymmetric.
Require Import ProofCheckingEuclid.lemma_right_triangle_NC.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_sumtwort.
Require Import ProofCheckingEuclid.lemma_s_supp.
Require Import ProofCheckingEuclid.proposition_28C.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_twoperpsparallel :
	forall A B C D,
	RightTriangle A B C ->
	RightTriangle B C D ->
	SameSide A D B C ->
	Par A B C D.
Proof.
	intros A B C D.
	intros RightTriangle_ABC.
	intros RightTriangle_BCD.
	intros SameSide_A_D_BC.

	assert (eq D D) as eq_D_D by (reflexivity).

	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_ABC RightTriangle_BCD) as CongA_ABC_BCD.

	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_ABC) as nCol_A_B_C.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (_ & neq_B_C & _ & _ & _ & _).

	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_BCD) as nCol_B_C_D.
	pose proof (lemma_NCdistinct _ _ _ nCol_B_C_D) as (_ & neq_C_D & _ & _ & _ & _).
	pose proof (lemma_s_onray_assert_ABB _ _ neq_C_D) as OnRay_CD_D.

	pose proof (postulate_Euclid2 _ _ neq_B_C) as (E & BetS_B_C_E).

	pose proof (lemma_betweennotequal _ _ _ BetS_B_C_E) as (neq_C_E & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_C_E) as neq_E_C.

	pose proof (lemma_s_supp _ _ _ _ _ OnRay_CD_D BetS_B_C_E) as Supp_BCD_DCE.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_B_C_E) as Col_B_C_E.
	pose proof (lemma_collinearright _ _ _ _ RightTriangle_BCD Col_B_C_E neq_E_C) as RightTriangle_ECD.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_ECD) as RightTriangle_DCE.

	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_BCD RightTriangle_DCE) as CongA_BCD_DCE.

	pose proof (lemma_s_sumtwort _ _ _ _ _ _ _ _ _ _ _ Supp_BCD_DCE CongA_ABC_BCD CongA_BCD_DCE) as SumTwoRT_ABC_BCD.

	pose proof (proposition_28C _ _ _ _ SumTwoRT_ABC_BCD SameSide_A_D_BC) as Par_BA_CD.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_BA_CD) as Par_CD_BA.
	pose proof (lemma_parallelflip _ _ _ _ Par_CD_BA) as (_ & Par_CD_AB & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_CD_AB) as Par_AB_CD.

	exact Par_AB_CD.
Qed.

End Euclid.

