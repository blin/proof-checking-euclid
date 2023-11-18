Require Import ProofCheckingEuclid.by_def_CongTriangles.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Euclid4.
Require Import ProofCheckingEuclid.lemma_squareparallelogram.
Require Import ProofCheckingEuclid.lemma_squarerectangle.
Require Import ProofCheckingEuclid.proposition_04.

Section Euclid.

Context `{Ax:area}.

Lemma lemma_squaresequal :
	forall A B C D a b c d,
	Cong A B a b ->
	Square A B C D ->
	Square a b c d ->
	EqAreaQuad A B C D a b c d.
Proof.
	intros A B C D a b c d.
	intros Cong_AB_ab.
	intros Square_A_B_C_D.
	intros Square_a_b_c_d.

	assert (Square_A_B_C_D_2 := Square_A_B_C_D).
	destruct Square_A_B_C_D_2 as (Cong_AB_CD & Cong_AB_BC & Cong_AB_DA & RightTriangle_DAB & RightTriangle_ABC & RightTriangle_BCD & RightTriangle_CDA).

	assert (Square_a_b_c_d_2 := Square_a_b_c_d).
	destruct Square_a_b_c_d_2 as (Cong_ab_cd & Cong_ab_bc & Cong_ab_da & RightTriangle_dab & RightTriangle_abc & RightTriangle_bcd & RightTriangle_cda).

	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_DAB RightTriangle_dab) as CongA_DAB_dab.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AB_DA) as Cong_DA_AB.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_DA_AB Cong_AB_ab) as Cong_DA_ab.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_DA_ab Cong_ab_da) as Cong_DA_da.
	pose proof (lemma_squareparallelogram _ _ _ _ Square_A_B_C_D) as Parallelogram_A_B_C_D.
	pose proof (lemma_squareparallelogram _ _ _ _ Square_a_b_c_d) as Parallelogram_a_b_c_d.
	assert (Parallelogram_A_B_C_D_2 := Parallelogram_A_B_C_D).
	destruct Parallelogram_A_B_C_D_2 as (Par_AB_CD & Par_AD_BC).
	assert (Parallelogram_a_b_c_d_2 := Parallelogram_a_b_c_d).
	destruct Parallelogram_a_b_c_d_2 as (Par_ab_cd & Par_ad_bc).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (_ & _ & _ & nCol_A_B_D).
	pose proof (by_prop_Par_NC _ _ _ _ Par_ab_cd) as (_ & _ & _ & nCol_a_b_d).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_DA_da) as (Cong_AD_ad & _ & _).
	pose proof (proposition_04 _ _ _ _ _ _ Cong_AD_ad Cong_AB_ab CongA_DAB_dab) as (Cong_DB_db & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_DB_db) as (Cong_BD_bd & _ & _).
	pose proof (by_def_Triangle _ _ _ nCol_A_B_D) as Triangle_ABD.
	pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_AB_ab Cong_BD_bd Cong_AD_ad) as CongTriangles_ABD_abd.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_ABD_abd) as EqAreaTri_ABD_abd.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_ABD_abd) as (EqAreaTri_ABD_bda & _ & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_ABD_bda) as EqAreaTri_bda_ABD.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_bda_ABD) as (EqAreaTri_bda_BDA & _ & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_bda_BDA) as EqAreaTri_BDA_bda.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AB_BC) as Cong_BC_AB.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_BC_AB Cong_AB_ab) as Cong_BC_ab.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_BC_ab Cong_ab_bc) as Cong_BC_bc.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AB_CD) as Cong_CD_AB.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_CD_AB Cong_AB_ab) as Cong_CD_ab.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_CD_ab Cong_ab_cd) as Cong_CD_cd.
	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (_ & _ & nCol_B_C_D & _).
	pose proof (by_def_Triangle _ _ _ nCol_B_C_D) as Triangle_BCD.
	pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_BC_bc Cong_CD_cd Cong_BD_bd) as CongTriangles_BCD_bcd.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_BCD_bcd) as EqAreaTri_BCD_bcd.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_BCD_bcd) as (_ & EqAreaTri_BCD_bdc & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_BCD_bdc) as EqAreaTri_bdc_BCD.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_bdc_BCD) as (_ & EqAreaTri_bdc_BDC & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_bdc_BDC) as EqAreaTri_BDC_bdc.
	pose proof (lemma_squarerectangle _ _ _ _ Square_A_B_C_D) as Rectangle_A_B_C_D.
	destruct Rectangle_A_B_C_D as (_ & _ & _ & _ & Cross_AC_BD).

	destruct Cross_AC_BD as (M & BetS_A_M_C & BetS_B_M_D).
	pose proof (lemma_squarerectangle _ _ _ _ Square_a_b_c_d) as Rectangle_a_b_c_d.
	destruct Rectangle_a_b_c_d as (_ & _ & _ & _ & Cross_ac_bd).

	destruct Cross_ac_bd as (m & BetS_a_m_c & BetS_b_m_d).

	assert (BetS B M D \/ eq B M \/ eq M D) as BetS_B_M_D' by (left; exact BetS_B_M_D).
	assert (BetS b m d \/ eq b m \/ eq m d) as BetS_b_m_d' by (left; exact BetS_b_m_d).

	pose proof (
		axiom_paste3
		B D A C M
		b d a c m
		EqAreaTri_BDA_bda
		EqAreaTri_BDC_bdc
		BetS_A_M_C
		BetS_B_M_D'
		BetS_a_m_c
		BetS_b_m_d'
	) as EqAreaQuad_BADC_badc.

	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_BADC_badc) as (_ & _ & _ & EqAreaQuad_BADC_abcd & _ & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_BADC_abcd) as EqAreaQuad_abcd_BADC.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_abcd_BADC) as (_ & _ & _ & EqAreaQuad_abcd_ABCD & _ & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_abcd_ABCD) as EqAreaQuad_ABCD_abcd.

	exact EqAreaQuad_ABCD_abcd.
Qed.

End Euclid.
