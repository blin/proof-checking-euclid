Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_Square.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_collinearparallel.
Require Import ProofCheckingEuclid.lemma_collinearright.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equaltorightisright.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_oppositesideflip.
Require Import ProofCheckingEuclid.lemma_oppositesidesymmetric.
Require Import ProofCheckingEuclid.lemma_parallelNC.
Require Import ProofCheckingEuclid.lemma_parallel_to_tarski_parallel.
Require Import ProofCheckingEuclid.lemma_parallelflip.
Require Import ProofCheckingEuclid.lemma_parallelsymmetric.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_right_triangle_NC.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.
Require Import ProofCheckingEuclid.lemma_supplementofright.
Require Import ProofCheckingEuclid.lemma_twoperpsparallel.
Require Import ProofCheckingEuclid.proposition_29.
Require Import ProofCheckingEuclid.proposition_33B.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_road_to_reality_2_7 :
	forall A B C D,
	RightTriangle A B C ->
	RightTriangle B C D ->
	Cong A B B C ->
	Cong B C C D ->
	SameSide D A B C ->
	Square A B C D.
Proof.
	intros A B C D.
	intros RightTriangle_ABC.
	intros RightTriangle_BCD.
	intros Cong_AB_BC.
	intros Cong_BC_CD.
	intros SameSide_D_A_BC.

	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq D D) as eq_D_D by (reflexivity).

	pose proof (by_def_Col_from_eq_A_C C D C eq_C_C) as Col_C_D_C.
	pose proof (by_def_Col_from_eq_B_C A D D eq_D_D) as Col_A_D_D.

	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_ABC) as nCol_A_B_C.
	pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_BCD) as nCol_B_C_D.

	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).

	pose proof (lemma_NCdistinct _ _ _ nCol_B_C_D) as (_ & neq_C_D & neq_B_D & _ & neq_D_C & neq_D_B).
	pose proof (lemma_NCorder _ _ _ nCol_B_C_D) as (nCol_C_B_D & nCol_C_D_B & nCol_D_B_C & nCol_B_D_C & nCol_D_C_B).

	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_AB_BC Cong_BC_CD) as Cong_AB_CD.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AB_CD) as (_ & _ & Cong_AB_DC).

	pose proof (lemma_samesidesymmetric _ _ _ _ SameSide_D_A_BC) as (SameSide_A_D_BC & _ & _).


	pose proof (lemma_twoperpsparallel _ _ _ _ RightTriangle_ABC RightTriangle_BCD SameSide_A_D_BC) as Par_AB_CD.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_AB_CD) as Par_CD_AB.
	pose proof (lemma_parallelflip _ _ _ _ Par_AB_CD) as (_ & Par_AB_DC & _).

	pose proof (lemma_parallelNC _ _ _ _ Par_AB_DC) as (nCol_A_B_D & nCol_A_D_C & _ & _).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_D) as (_ & _ & neq_A_D & _ & _ & neq_D_A).

	pose proof (proposition_33B _ _ _ _ Par_AB_DC Cong_AB_DC SameSide_A_D_BC) as (Par_AD_BC & Cong_AD_BC).

	pose proof (lemma_parallelflip _ _ _ _ Par_AD_BC) as (_ & _ & Par_DA_CB).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AD_BC) as Cong_BC_AD.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_BC_AD) as (_ & _ & Cong_BC_DA).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_AB_BC Cong_BC_DA) as Cong_AB_DA.

	pose proof (lemma_parallel_to_tarski_parallel _ _ _ _ Par_CD_AB) as TarskiPar_CD_AB.
	destruct TarskiPar_CD_AB as (_ & _ & _ & SameSide_A_B_CD).

	pose proof (lemma_parallel_to_tarski_parallel _ _ _ _ Par_AD_BC) as TarskiPar_AD_BC.
	destruct TarskiPar_AD_BC as (_ & _ & _ & SameSide_B_C_AD).

	pose proof (postulate_Euclid2 _ _ neq_A_D) as (E & BetS_A_D_E).
	pose proof (postulate_Euclid2 _ _ neq_B_A) as (G & BetS_B_A_G).
	pose proof (postulate_Euclid2 _ _ neq_B_C) as (H & BetS_B_C_H).
	pose proof (postulate_Euclid2 _ _ neq_C_D) as (F & BetS_C_D_F).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_E) as BetS_E_D_A.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_G) as BetS_G_A_B.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_C_H) as BetS_H_C_B.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_D_F) as BetS_F_D_C.

	pose proof (lemma_betweennotequal _ _ _ BetS_B_A_G) as (neq_A_G & _ & neq_B_G).
	pose proof (lemma_betweennotequal _ _ _ BetS_C_D_F) as (neq_D_F & _ & neq_C_F).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_D_A) as (_ & neq_E_D & neq_E_A).
	pose proof (lemma_betweennotequal _ _ _ BetS_H_C_B) as (_ & neq_H_C & neq_H_B).
	pose proof (lemma_inequalitysymmetric _ _ neq_B_G) as neq_G_B.
	pose proof (lemma_inequalitysymmetric _ _ neq_C_F) as neq_F_C.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_D_E) as Col_A_D_E.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_A_G) as Col_B_A_G.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_C_H) as Col_B_C_H.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_D_F) as Col_C_D_F.
	pose proof (lemma_collinearorder _ _ _ Col_A_D_E) as (Col_D_A_E & Col_D_E_A & Col_E_A_D & Col_A_E_D & Col_E_D_A).
	pose proof (lemma_collinearorder _ _ _ Col_B_A_G) as (Col_A_B_G & Col_A_G_B & Col_G_B_A & Col_B_G_A & Col_G_A_B).
	pose proof (lemma_collinearorder _ _ _ Col_B_C_H) as (Col_C_B_H & Col_C_H_B & Col_H_B_C & Col_B_H_C & Col_H_C_B).
	pose proof (lemma_collinearorder _ _ _ Col_C_D_F) as (Col_D_C_F & Col_D_F_C & Col_F_C_D & Col_C_F_D & Col_F_D_C).

	pose proof (lemma_collinearparallel _ _ _ _ _ Par_DA_CB Col_C_B_H neq_H_B) as Par_DA_HB.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_DA_HB) as Par_HB_DA.
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_HB_DA Col_D_A_E neq_E_A) as Par_HB_EA.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_HB_EA) as Par_EA_HB.
	pose proof (lemma_parallelflip _ _ _ _ Par_EA_HB) as (Par_AE_HB & Par_EA_BH & Par_AE_BH).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_AB_DC Col_D_C_F neq_F_C) as Par_AB_FC.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_AB_FC) as Par_FC_AB.
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_FC_AB Col_A_B_G neq_G_B) as Par_FC_GB.

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_B_C_H Col_C_D_C nCol_C_D_B) as OppositeSide_B_CD_H.
	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_C_D_F Col_A_D_D nCol_A_D_C) as OppositeSide_C_AD_F.

	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_A_B_CD OppositeSide_B_CD_H) as OppositeSide_A_CD_H.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_B_C_AD OppositeSide_C_AD_F) as OppositeSide_B_AD_F.

	pose proof (lemma_oppositesidesymmetric _ _ _ _ OppositeSide_B_AD_F) as OppositeSide_F_AD_B.
	pose proof (lemma_oppositesideflip _ _ _ _ OppositeSide_A_CD_H) as OppositeSide_A_DC_H.
	pose proof (lemma_oppositesideflip _ _ _ _ OppositeSide_F_AD_B) as OppositeSide_F_DA_B.

	pose proof (proposition_29 _ _ _ _ _ _ _ Par_AE_BH BetS_A_D_E BetS_B_C_H BetS_F_D_C OppositeSide_A_DC_H) as (CongA_ADC_DCH & _ & _).
	pose proof (proposition_29 _ _ _ _ _ _ _ Par_FC_GB BetS_F_D_C BetS_G_A_B BetS_E_D_A OppositeSide_F_DA_B) as (_ & _ & SumTwoRT_CDA_DAB).

	pose proof (lemma_collinearright _ _ _ _ RightTriangle_BCD Col_B_C_H neq_H_C) as RightTriangle_HCD.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_HCD) as RightTriangle_DCH.
	pose proof (lemma_equaltorightisright _ _ _ _ _ _ RightTriangle_DCH CongA_ADC_DCH) as RightTriangle_ADC.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_ADC) as RightTriangle_CDA.

	destruct SumTwoRT_CDA_DAB as (X & Y & Z & U & V & Supp_XYU_VYZ & CongA_CDA_XYU & CongA_DAB_VYZ).

	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_CDA_XYU) as CongA_XYU_CDA.
	pose proof (lemma_equaltorightisright _ _ _ _ _ _ RightTriangle_CDA CongA_XYU_CDA) as RightTriangle_XYU.

	pose proof (lemma_supplementofright _ _ _ _ _ Supp_XYU_VYZ RightTriangle_XYU) as (_ & RightTriangle_VYZ).
	pose proof (lemma_equaltorightisright _ _ _ _ _ _ RightTriangle_VYZ CongA_DAB_VYZ) as RightTriangle_DAB.

	pose proof (by_def_Square _ _ _ _ Cong_AB_CD Cong_AB_BC Cong_AB_DA RightTriangle_DAB RightTriangle_ABC RightTriangle_BCD RightTriangle_CDA) as Square_A_B_C_D.

	exact Square_A_B_C_D.
Qed.

End Euclid.
