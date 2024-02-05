Require Import ProofCheckingEuclid.by_def_CongTriangles.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B .
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_Lt_trichotomous.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_equaltoright.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Euclid4.
Require Import ProofCheckingEuclid.lemma_crossimpliesopposite.
Require Import ProofCheckingEuclid.lemma_squareparallelogram.
Require Import ProofCheckingEuclid.lemma_squarerectangle.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_34.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_48A :
	forall A B C D a b c d,
	Square A B C D ->
	Square a b c d ->
	EqAreaQuad A B C D a b c d ->
	Cong A B a b.
Proof.
	intros A B C D a b c d.
	intros Square_A_B_C_D.
	intros Square_a_b_c_d.
	intros EqAreaQuad_ABCD_abcd.


	assert (Square_A_B_C_D_2 := Square_A_B_C_D).
	destruct Square_A_B_C_D_2 as (_ & _ & Cong_AB_DA & RightTriangle_DAB & _ & _ & _).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_DA) as (_ & _ & Cong_AB_AD).

	pose proof (lemma_squarerectangle _ _ _ _ Square_A_B_C_D) as Rectangle_A_B_C_D.
	assert (Rectangle_A_B_C_D_2 := Rectangle_A_B_C_D).
	destruct Rectangle_A_B_C_D as (_ & _ & _ & _ & Cross_AC_BD).

	pose proof (lemma_squareparallelogram _ _ _ _ Square_A_B_C_D) as Parallelogram_A_B_C_D.
	assert (Parallelogram_A_B_C_D_2 := Parallelogram_A_B_C_D).
	destruct Parallelogram_A_B_C_D_2 as (Par_AB_CD & Par_AD_BC).

	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (_ & _ & _ & nCol_A_B_D).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_D) as (_ & _ & nCol_D_A_B & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_D) as (neq_A_B & _ & _ & _ & _ & _).
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_D_A_B) as CongA_DAB_DAB.

	pose proof (by_def_Triangle _ _ _ nCol_D_A_B) as Triangle_DAB.

	pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_AC_BD nCol_A_B_D) as (OppositeSide_A_BD_C & _ & _ & _).

	assert (Square_a_b_c_d_2 := Square_a_b_c_d).
	destruct Square_a_b_c_d_2 as (_ & _ & Cong_ab_da & RightTriangle_dab & _ & _ & _).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_ab_da) as (_ & _ & Cong_ab_ad).

	pose proof (lemma_squarerectangle _ _ _ _ Square_a_b_c_d) as Rectangle_a_b_c_d.
	assert (Rectangle_a_b_c_d_2 := Rectangle_a_b_c_d).
	destruct Rectangle_a_b_c_d as (_ & _ & _ & _ & Cross_ac_bd).

	pose proof (lemma_squareparallelogram _ _ _ _ Square_a_b_c_d) as Parallelogram_a_b_c_d.
	assert (Parallelogram_a_b_c_d_2 := Parallelogram_a_b_c_d).
	destruct Parallelogram_a_b_c_d_2 as (Par_ab_cd & Par_ad_bc).

	pose proof (by_prop_Par_NC _ _ _ _ Par_ab_cd) as (_ & _ & _ & nCol_a_b_d).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_a_b_d) as (neq_a_b & _ & _ & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_a_b_d) as (_ & _ & nCol_d_a_b & _ & _).
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_d_a_b) as CongA_dab_dab.

	pose proof (by_def_Triangle _ _ _ nCol_d_a_b) as Triangle_dab.

	pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_ac_bd nCol_a_b_d) as (OppositeSide_a_bd_c & _ & _ & _).

	pose proof (proposition_34 _ _ _ _ Parallelogram_A_B_C_D) as (_ & _ & _ & _ & CongTriangles_BAD_DCB).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_BAD_DCB) as EqAreaTri_BAD_DCB.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_BAD_DCB) as (_ & _ & _ & _ & EqAreaTri_BAD_BDC).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_BAD_BDC) as EqAreaTri_BDC_BAD.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_BDC_BAD) as (_ & _ & EqAreaTri_BDC_ABD & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_BDC_ABD) as EqAreaTri_ABD_BDC.

	pose proof (proposition_34 _ _ _ _ Parallelogram_a_b_c_d) as (_ & _ & _ & _ & CongTriangles_bad_dcb).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_bad_dcb) as EqAreaTri_bad_dcb.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_bad_dcb) as (_ & _ & _ & _ & EqAreaTri_bad_bdc).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_bad_bdc) as EqAreaTri_bdc_bad.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_bdc_bad) as (_ & _ & EqAreaTri_bdc_abd & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_bdc_abd) as EqAreaTri_abd_bdc.

	pose proof (
		axiom_halvesofequals
		_ _ _ _ _ _ _ _
		EqAreaTri_ABD_BDC OppositeSide_A_BD_C EqAreaTri_abd_bdc OppositeSide_a_bd_c EqAreaQuad_ABCD_abcd
	) as EqAreaTri_ABD_abd.

	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_ABD_abd) as EqAreaTri_abd_ABD.


	assert (~ Lt a b A B) as n_Lt_ab_AB.
	{
		intro Lt_ab_AB.

		pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_ab_AB Cong_ab_ad) as Lt_ad_AB.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_ad_AB Cong_AB_AD) as Lt_ad_AD.

		assert (Lt_ab_AB_2 := Lt_ab_AB).
		destruct Lt_ab_AB_2 as (E & BetS_A_E_B & Cong_AE_ab).

		pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_A_E_B neq_A_B) as OnRay_AB_E.


		destruct Lt_ad_AD as (F & BetS_A_F_D & Cong_AF_ad).

		pose proof (by_prop_BetS_notequal _ _ _ BetS_A_F_D) as (_ & _ & neq_A_D).

		pose proof (by_prop_Cong_flip _ _ _ _ Cong_AF_ad) as (Cong_FA_da & _ & _).

		pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_A_F_D neq_A_D) as OnRay_AD_F.

		pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_DAB_DAB OnRay_AD_F OnRay_AB_E) as CongA_DAB_FAE.
		pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_DAB_FAE) as CongA_FAE_DAB.

		pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_DAB CongA_FAE_DAB) as RightTriangle_FAE.
		pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_FAE RightTriangle_dab) as CongA_FAE_dab.
		pose proof (proposition_04 _ _ _ _ _ _ Cong_AF_ad Cong_AE_ab CongA_FAE_dab) as (Cong_FE_db & _ & _).
		pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_FA_da Cong_AE_ab Cong_FE_db) as CongTriangles_FAE_dab.
		pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_FAE_dab) as EqAreaTri_FAE_dab.
		pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_FAE_dab) as (EqAreaTri_FAE_abd & _ & _ & _ & _).
		pose proof (axiom_EqAreaTri_transitive _ _ _ _ _ _ _ _ _ EqAreaTri_FAE_abd EqAreaTri_abd_ABD) as EqAreaTri_FAE_ABD.
		pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_FAE_ABD) as (_ & _ & _ & _ & EqAreaTri_FAE_DAB).
		pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_FAE_DAB) as EqAreaTri_DAB_FAE.

		pose proof (axiom_deZolt2 _ _ _ _ _ Triangle_DAB BetS_A_F_D BetS_A_E_B) as n_EqAreaTri_DAB_FAE.

		contradict EqAreaTri_DAB_FAE.
		exact n_EqAreaTri_DAB_FAE.
	}


	assert (~ Lt A B a b) as n_Lt_AB_ab.
	{
		intro Lt_AB_ab.

		pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_AB_ab Cong_AB_AD) as Lt_AD_ab.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_AD_ab Cong_ab_ad) as Lt_AD_ad.

		assert (Lt_AB_ab_2 := Lt_AB_ab).
		destruct Lt_AB_ab_2 as (e & BetS_a_e_b & Cong_ae_AB).

		pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_a_e_b neq_a_b) as OnRay_ab_e.

		destruct Lt_AD_ad as (f & BetS_a_f_d & Cong_af_AD).

		pose proof (by_prop_BetS_notequal _ _ _ BetS_a_f_d) as (_ & _ & neq_a_d).

		pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_a_f_d neq_a_d) as OnRay_ad_f.

		pose proof (by_prop_Cong_flip _ _ _ _ Cong_af_AD) as (Cong_fa_DA & _ & _).


		pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_dab_dab OnRay_ad_f OnRay_ab_e) as CongA_dab_fae.
		pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_dab_fae) as CongA_fae_dab.
		pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_dab CongA_fae_dab) as RightTriangle_fae.
		pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_fae RightTriangle_DAB) as CongA_fae_DAB.
		pose proof (proposition_04 _ _ _ _ _ _ Cong_af_AD Cong_ae_AB CongA_fae_DAB) as (Cong_fe_DB & _ & _).
		pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_fa_DA Cong_ae_AB Cong_fe_DB) as CongTriangles_fae_DAB.
		pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_fae_DAB) as EqAreaTri_fae_DAB.
		pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_fae_DAB) as (EqAreaTri_fae_ABD & _ & _ & _ & _).
		pose proof (axiom_EqAreaTri_transitive _ _ _ _ _ _ _ _ _ EqAreaTri_fae_ABD EqAreaTri_ABD_abd) as EqAreaTri_fae_abd.
		pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_fae_abd) as (_ & _ & _ & _ & EqAreaTri_fae_dab).
		pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_fae_dab) as EqAreaTri_dab_fae.

		pose proof (axiom_deZolt2 _ _ _ _ _ Triangle_dab BetS_a_f_d BetS_a_e_b) as n_EqAreaTri_dab_fae.

		contradict EqAreaTri_dab_fae.
		exact n_EqAreaTri_dab_fae.
	}

	pose proof (by_prop_Lt_trichotomous _ _ _ _ n_Lt_AB_ab n_Lt_ab_AB neq_A_B neq_a_b) as Cong_AB_ab.

	exact Cong_AB_ab.
Qed.

End Euclid.
