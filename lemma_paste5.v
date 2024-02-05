Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E .
Require Import ProofCheckingEuclid.by_def_SameSide.
Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col .
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_SameSide_not_OppositeSide.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_crisscross.
Require Import ProofCheckingEuclid.lemma_crossimpliesopposite.
Require Import ProofCheckingEuclid.lemma_diagonalsmeet.
Require Import ProofCheckingEuclid.lemma_rectangleparallelogram.
Require Import ProofCheckingEuclid.lemma_sameside_onray_EFAC_BFG_EGAC.
Require Import ProofCheckingEuclid.proposition_34.

Section Euclid.

Context `{Ax:area}.

Lemma lemma_paste5 :
	forall B C D E L M b c d e l m,
	EqAreaQuad B M L D b m l d ->
	EqAreaQuad M C E L m c e l ->
	BetS B M C ->
	BetS b m c ->
	BetS E L D ->
	BetS e l d ->
	Rectangle M C E L ->
	Rectangle m c e l ->
	EqAreaQuad B C E D b c e d.
Proof.
	intros B C D E L M b c d e l m.
	intros EqAreaQuad_BMLD_bmld.
	intros EqAreaQuad_MCEL_mcel.
	intros BetS_B_M_C.
	intros BetS_b_m_c.
	intros BetS_E_L_D.
	intros BetS_e_l_d.
	intros Rectangle_M_C_E_L.
	intros Rectangle_m_c_e_l.

	pose proof (lemma_rectangleparallelogram _ _ _ _ Rectangle_M_C_E_L) as Parallelogram_M_C_E_L.
	pose proof (lemma_rectangleparallelogram _ _ _ _ Rectangle_m_c_e_l) as Parallelogram_m_c_e_l.
	pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_M_C_E_L) as (P & BetS_M_P_E & BetS_C_P_L).
	pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_m_c_e_l) as (p & BetS_m_p_e & BetS_c_p_l).
	assert (Parallelogram_M_C_E_L_2 := Parallelogram_M_C_E_L).
	destruct Parallelogram_M_C_E_L_2 as (Par_MC_EL & Par_ML_CE).
	pose proof (by_prop_Par_NC _ _ _ _ Par_MC_EL) as (_ & _ & _ & nCol_M_C_L).
	assert (Parallelogram_m_c_e_l_2 := Parallelogram_m_c_e_l).
	destruct Parallelogram_m_c_e_l_2 as (Par_mc_el & Par_ml_ce).
	pose proof (by_prop_Par_NC _ _ _ _ Par_mc_el) as (_ & _ & _ & nCol_m_c_l).
	pose proof (proposition_34 _ _ _ _ Parallelogram_M_C_E_L) as (_ & _ & _ & _ & CongTriangles_CML_LEC).
	pose proof (proposition_34 _ _ _ _ Parallelogram_m_c_e_l) as (_ & _ & _ & _ & CongTriangles_cml_lec).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_CML_LEC) as EqAreaTri_CML_LEC.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_cml_lec) as EqAreaTri_cml_lec.

	destruct Rectangle_M_C_E_L as (_ & _ & _ & _ & Cross_ME_CL).
	destruct Rectangle_m_c_e_l as (_ & _ & _ & _ & Cross_me_cl).
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_cml_lec) as (_ & _ & _ & _ & EqAreaTri_cml_cle).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_cml_cle) as EqAreaTri_cle_cml.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_cle_cml) as (_ & _ & EqAreaTri_cle_mcl & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_cle_mcl) as EqAreaTri_mcl_cle.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_CML_LEC) as (_ & _ & _ & _ & EqAreaTri_CML_CLE).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_CML_CLE) as EqAreaTri_CLE_CML.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_CLE_CML) as (_ & _ & EqAreaTri_CLE_MCL & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_CLE_MCL) as EqAreaTri_MCL_CLE.
	pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_ME_CL nCol_M_C_L) as (OppositeSide_M_CL_E & _ & _ & _).
	pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_me_cl nCol_m_c_l) as (OppositeSide_m_cl_e & _ & _ & _).
	pose proof (axiom_halvesofequals _ _ _ _ _ _ _ _ EqAreaTri_MCL_CLE OppositeSide_M_CL_E EqAreaTri_mcl_cle OppositeSide_m_cl_e EqAreaQuad_MCEL_mcel) as EqAreaTri_MCL_mcl.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_MCEL_mcel) as (_ & _ & _ & _ & _ & EqAreaQuad_MCEL_ecml & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_MCEL_ecml) as EqAreaQuad_ecml_MCEL.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_ecml_MCEL) as (_ & _ & _ & _ & _ & EqAreaQuad_ecml_ECML & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_ecml_ECML) as EqAreaQuad_ECML_ecml.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_M_CL_E) as OppositeSide_E_CL_M.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_m_cl_e) as OppositeSide_e_cl_m.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_MCL_CLE) as (_ & _ & _ & _ & EqAreaTri_MCL_ECL).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_MCL_ECL) as EqAreaTri_ECL_MCL.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_ECL_MCL) as (EqAreaTri_ECL_CLM & _ & _ & _ & _).
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_mcl_cle) as (_ & _ & _ & _ & EqAreaTri_mcl_ecl).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_mcl_ecl) as EqAreaTri_ecl_mcl.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_ecl_mcl) as (EqAreaTri_ecl_clm & _ & _ & _ & _).
	pose proof (axiom_halvesofequals _ _ _ _ _ _ _ _ EqAreaTri_ECL_CLM OppositeSide_E_CL_M EqAreaTri_ecl_clm OppositeSide_e_cl_m EqAreaQuad_ECML_ecml) as EqAreaTri_ECL_ecl.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_BMLD_bmld) as (_ & _ & _ & _ & EqAreaQuad_BMLD_dbml & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_BMLD_dbml) as EqAreaQuad_dbml_BMLD.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_dbml_BMLD) as (_ & _ & _ & _ & EqAreaQuad_dbml_DBML & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_dbml_DBML) as EqAreaQuad_DBML_dbml.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_M_C) as Col_B_M_C.
	pose proof (by_prop_Col_order _ _ _ Col_B_M_C) as (_ & Col_M_C_B & _ & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_M_C) as (_ & _ & neq_B_C).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_MC_EL) as Par_EL_MC.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_EL_MC Col_M_C_B neq_B_C) as Par_EL_BC.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_EL_BC) as Par_BC_EL.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_L_D) as Col_E_L_D.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_L_D) as (neq_L_D & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_L_D) as neq_D_L.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_BC_EL Col_E_L_D neq_D_L) as Par_BC_DL.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_L_D) as (_ & neq_E_L & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_M_C) as (neq_M_C & _ & _).

	assert (Par_EL_MC_2 := Par_EL_MC).
	destruct Par_EL_MC_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_E_L_M_C & _ & _).

	assert (~ Cross B D C L) as n_Cross_BD_CL.
	{
		intro Cross_BD_CL.

		assert (~ Col C L M) as n_Col_C_L_M.
		{
			intro Col_C_L_M.
			pose proof (by_prop_Col_order _ _ _ Col_C_L_M) as (_ & _ & Col_M_C_L & _ & _).
			assert (eq L L) as eq_L_L by (reflexivity).
			pose proof (by_def_Col_from_eq_B_C E L L eq_L_L) as Col_E_L_L.
			pose proof (by_def_Meet _ _ _ _ _ neq_E_L neq_M_C Col_E_L_L Col_M_C_L) as Meet_E_L_M_C.

			contradict Meet_E_L_M_C.
			exact n_Meet_E_L_M_C.
		}
		pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_C_L_M) as nCol_C_L_M.


		assert (~ Col C L D) as n_Col_C_L_D.
		{
			intro Col_C_L_D.
			pose proof (by_prop_Col_order _ _ _ Col_C_L_D) as (_ & _ & _ & _ & Col_D_L_C).
			pose proof (by_prop_Col_order _ _ _ Col_E_L_D) as (_ & _ & _ & _ & Col_D_L_E).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_L_E Col_D_L_C neq_D_L) as Col_L_E_C.
			pose proof (by_prop_Col_order _ _ _ Col_L_E_C) as (Col_E_L_C & _ & _ & _ & _).
			assert (eq C C) as eq_C_C by (reflexivity).
			pose proof (by_def_Col_from_eq_B_C M C C eq_C_C) as Col_M_C_C.
			pose proof (by_def_Meet _ _ _ _ _ neq_E_L neq_M_C Col_E_L_C Col_M_C_C) as Meet_E_L_M_C.
			contradict Meet_E_L_M_C.
			exact n_Meet_E_L_M_C.
		}
		pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_C_L_D) as nCol_C_L_D.

		assert (eq L L) as eq_L_L by (reflexivity).
		pose proof (by_def_Col_from_eq_B_C C L L eq_L_L) as Col_C_L_L.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_L_D) as BetS_D_L_E.
		pose proof (by_def_Col_from_BetS_A_C_B _ _ _ BetS_C_P_L) as Col_C_L_P.
		pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_C_L_L Col_C_L_P BetS_D_L_E BetS_M_P_E nCol_C_L_D nCol_C_L_M) as SameSide_D_M_CL.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_C) as BetS_C_M_B.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_C_M_B) as (_ & neq_C_M & _).

		pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_C_M_B neq_C_M) as OnRay_CM_B.

		assert (eq C C) as eq_C_C by (reflexivity).
		pose proof (by_def_Col_from_eq_A_B C C L eq_C_C) as Col_C_C_L.
		pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_D_M_CL Col_C_C_L OnRay_CM_B) as SameSide_D_B_CL.
		pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_D_B_CL) as (SameSide_B_D_CL & _ & _).
		pose proof (by_prop_SameSide_not_OppositeSide _ _ _ _ SameSide_B_D_CL) as n_OppositeSide_B_CL_D.

		assert (~ Col B C L) as n_Col_B_C_L.
		{
			intro Col_B_C_L.
			pose proof (by_prop_Col_order _ _ _ Col_B_M_C) as (_ & _ & _ & Col_B_C_M & _).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_C_M Col_B_C_L neq_B_C) as Col_C_M_L.
			pose proof (by_prop_Col_order _ _ _ Col_C_M_L) as (Col_M_C_L & _ & _ & _ & _).
			pose proof (by_def_Col_from_eq_B_C E L L eq_L_L) as Col_E_L_L.
			pose proof (by_def_Meet _ _ _ _ _ neq_E_L neq_M_C Col_E_L_L Col_M_C_L) as Meet_E_L_M_C.
			contradict Meet_E_L_M_C.
			exact n_Meet_E_L_M_C.
		}
		pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_B_C_L) as nCol_B_C_L.

		pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_BD_CL nCol_B_C_L) as (OppositeSide_B_CL_D & _ & _ & _).
		contradict OppositeSide_B_CL_D.
		exact n_OppositeSide_B_CL_D.
	}

	pose proof (lemma_crisscross _ _ _ _ Par_BC_DL n_Cross_BD_CL) as Cross_BL_DC.

	destruct Cross_BL_DC as (R & BetS_B_R_L & BetS_D_R_C).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_b_m_c) as Col_b_m_c.
	pose proof (by_prop_Col_order _ _ _ Col_b_m_c) as (_ & Col_m_c_b & _ & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_b_m_c) as (_ & _ & neq_b_c).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_mc_el) as Par_el_mc.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_el_mc Col_m_c_b neq_b_c) as Par_el_bc.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_el_bc) as Par_bc_el.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_e_l_d) as Col_e_l_d.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_e_l_d) as (neq_l_d & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_l_d) as neq_d_l.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_bc_el Col_e_l_d neq_d_l) as Par_bc_dl.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_e_l_d) as (_ & neq_e_l & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_b_m_c) as (neq_m_c & _ & _).

	assert (Par_el_mc_2 := Par_el_mc).
	destruct Par_el_mc_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_e_l_m_c & _ & _).

	assert (~ Cross b d c l) as n_Cross_bd_cl.
	{
		intro Cross_bd_cl.

		assert (~ Col c l m) as n_Col_c_l_m.
		{
			intro Col_c_l_m.
			pose proof (by_prop_Col_order _ _ _ Col_c_l_m) as (_ & _ & Col_m_c_l & _ & _).
			assert (eq l l) as eq_l_l by (reflexivity).
			pose proof (by_def_Col_from_eq_B_C e l l eq_l_l) as Col_e_l_l.
			pose proof (by_def_Meet _ _ _ _ _ neq_e_l neq_m_c Col_e_l_l Col_m_c_l) as Meet_e_l_m_c.
			contradict Meet_e_l_m_c.
			exact n_Meet_e_l_m_c.
		}
		pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_c_l_m) as nCol_c_l_m.


		assert (~ Col c l d) as n_Col_c_l_d.
		{
			intro Col_c_l_d.
			pose proof (by_prop_Col_order _ _ _ Col_c_l_d) as (_ & _ & _ & _ & Col_d_l_c).
			pose proof (by_prop_Col_order _ _ _ Col_e_l_d) as (_ & _ & _ & _ & Col_d_l_e).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_d_l_e Col_d_l_c neq_d_l) as Col_l_e_c.
			pose proof (by_prop_Col_order _ _ _ Col_l_e_c) as (Col_e_l_c & _ & _ & _ & _).
			assert (eq c c) as eq_c_c by (reflexivity).
			pose proof (by_def_Col_from_eq_B_C m c c eq_c_c) as Col_m_c_c.
			pose proof (by_def_Meet _ _ _ _ _ neq_e_l neq_m_c Col_e_l_c Col_m_c_c) as Meet_e_l_m_c.
			contradict Meet_e_l_m_c.
			exact n_Meet_e_l_m_c.
		}
		pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_c_l_d) as nCol_c_l_d.

		assert (eq l l) as eq_l_l by (reflexivity).
		pose proof (by_def_Col_from_eq_B_C c l l eq_l_l) as Col_c_l_l.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_e_l_d) as BetS_d_l_e.
		pose proof (by_def_Col_from_BetS_A_C_B _ _ _ BetS_c_p_l) as Col_c_l_p.
		pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_c_l_l Col_c_l_p BetS_d_l_e BetS_m_p_e nCol_c_l_d nCol_c_l_m) as SameSide_d_m_cl.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_b_m_c) as BetS_c_m_b.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_c_m_b) as (_ & neq_c_m & _).

		pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_c_m_b neq_c_m) as OnRay_cm_b.

		assert (eq c c) as eq_c_c by (reflexivity).
		pose proof (by_def_Col_from_eq_A_B c c l eq_c_c) as Col_c_c_l.
		pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_d_m_cl Col_c_c_l OnRay_cm_b) as SameSide_d_b_cl.
		pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_d_b_cl) as (SameSide_b_d_cl & _ & _).
		pose proof (by_prop_SameSide_not_OppositeSide _ _ _ _ SameSide_b_d_cl) as n_OppositeSide_b_cl_d.

		assert (~ Col b c l) as n_Col_b_c_l.
		{
			intro Col_b_c_l.
			pose proof (by_prop_Col_order _ _ _ Col_b_m_c) as (_ & _ & _ & Col_b_c_m & _).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_b_c_m Col_b_c_l neq_b_c) as Col_c_m_l.
			pose proof (by_prop_Col_order _ _ _ Col_c_m_l) as (Col_m_c_l & _ & _ & _ & _).
			pose proof (by_def_Col_from_eq_B_C e l l eq_l_l) as Col_e_l_l.
			pose proof (by_def_Meet _ _ _ _ _ neq_e_l neq_m_c Col_e_l_l Col_m_c_l) as Meet_e_l_m_c.
			contradict Meet_e_l_m_c.
			exact n_Meet_e_l_m_c.
		}
		pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_b_c_l) as nCol_b_c_l.

		pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_bd_cl nCol_b_c_l) as (OppositeSide_b_cl_d & _ & _ & _).
		contradict OppositeSide_b_cl_d.
		exact n_OppositeSide_b_cl_d.
	}

	pose proof (lemma_crisscross _ _ _ _ Par_bc_dl n_Cross_bd_cl) as Cross_bl_dc.

	destruct Cross_bl_dc as (r & BetS_b_r_l & BetS_d_r_c).
	pose proof (cn_sumofparts_Quad_Tri_sharedside _ _ _ _ _ _ _ _ _ _ _ _ BetS_B_M_C BetS_b_m_c EqAreaTri_MCL_mcl EqAreaQuad_DBML_dbml BetS_D_R_C BetS_B_R_L BetS_d_r_c BetS_b_r_l) as EqAreaQuad_DBCL_dbcl.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_DBCL_dbcl) as (_ & _ & _ & EqAreaQuad_DBCL_bdlc & _ & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_DBCL_bdlc) as EqAreaQuad_bdlc_DBCL.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_bdlc_DBCL) as (_ & _ & _ & EqAreaQuad_bdlc_BDLC & _ & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_bdlc_BDLC) as EqAreaQuad_BDLC_bdlc.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_ECL_ecl) as (_ & _ & _ & _ & EqAreaTri_ECL_lec).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_ECL_lec) as EqAreaTri_lec_ECL.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_lec_ECL) as (_ & _ & _ & _ & EqAreaTri_lec_LEC).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_lec_LEC) as EqAreaTri_LEC_lec.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_L_D) as BetS_D_L_E.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_e_l_d) as BetS_d_l_e.
	pose proof (by_prop_Par_flip _ _ _ _ Par_BC_EL) as (_ & Par_BC_LE & _).
	pose proof (by_prop_Col_order _ _ _ Col_E_L_D) as (Col_L_E_D & _ & _ & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_L_D) as (_ & _ & neq_E_D).
	pose proof (by_prop_neq_symmetric _ _ neq_E_D) as neq_D_E.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_BC_LE Col_L_E_D neq_D_E) as Par_BC_DE.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_ML_CE) as Par_CE_ML.
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_CE_ML) as TarskiPar_CE_ML.

	assert (TarskiPar_CE_ML_2 := TarskiPar_CE_ML).
	destruct TarskiPar_CE_ML_2 as (neq_C_E & neq_M_L & n_Meet_C_E_M_L & SameSide_M_L_CE).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_M_L_CE) as (SameSide_L_M_CE & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_M_C) as neq_C_M.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_C) as BetS_C_M_B.

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_C_M_B neq_C_M) as OnRay_CM_B.

	assert (eq C C) as eq_C_C by (reflexivity).
	pose proof (by_def_Col_from_eq_A_B C C E eq_C_C) as Col_C_C_E.
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_L_M_CE Col_C_C_E OnRay_CM_B) as SameSide_L_B_CE.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_L_B_CE) as (SameSide_B_L_CE & _ & _).

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_E_L_D neq_E_L) as OnRay_EL_D.

	assert (eq E E) as eq_E_E by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C C E E eq_E_E) as Col_C_E_E.
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_B_L_CE Col_C_E_E OnRay_EL_D) as SameSide_B_D_CE.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_B_D_CE) as (SameSide_D_B_CE & _ & _).

	assert (Par_BC_DE_2 := Par_BC_DE).
	destruct Par_BC_DE_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_B_C_D_E & _ & _).

	assert (~ Cross B D C E) as n_Cross_BD_CE.
	{
		intro Cross_BD_CE.

		assert (~ Col B C E) as n_Col_B_C_E.
		{
			intro Col_B_C_E.
			pose proof (by_def_Col_from_eq_B_C D E E eq_E_E) as Col_D_E_E.
			pose proof (by_def_Meet _ _ _ _ _ neq_B_C neq_D_E Col_B_C_E Col_D_E_E) as Meet_B_C_D_E.
			contradict Meet_B_C_D_E.
			exact n_Meet_B_C_D_E.
		}
		pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_B_C_E) as nCol_B_C_E.

		pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_BD_CE nCol_B_C_E) as (OppositeSide_B_CE_D & _ & _ & _).
		pose proof (by_prop_SameSide_not_OppositeSide _ _ _ _ SameSide_B_D_CE) as n_OppositeSide_B_CE_D.
		contradict OppositeSide_B_CE_D.
		exact n_OppositeSide_B_CE_D.
	}

	pose proof (lemma_crisscross _ _ _ _ Par_BC_DE n_Cross_BD_CE) as Cross_BE_DC.

	destruct Cross_BE_DC as (T & BetS_B_T_E & BetS_D_T_C).
	pose proof (by_prop_Par_flip _ _ _ _ Par_bc_el) as (_ & Par_bc_le & _).
	pose proof (by_prop_Col_order _ _ _ Col_e_l_d) as (Col_l_e_d & _ & _ & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_e_l_d) as (_ & _ & neq_e_d).
	pose proof (by_prop_neq_symmetric _ _ neq_e_d) as neq_d_e.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_bc_le Col_l_e_d neq_d_e) as Par_bc_de.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_ml_ce) as Par_ce_ml.
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_ce_ml) as TarskiPar_ce_ml.

	assert (TarskiPar_ce_ml_2 := TarskiPar_ce_ml).
	destruct TarskiPar_ce_ml_2 as (neq_c_e & neq_m_l & n_Meet_c_e_m_l & SameSide_m_l_ce).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_m_l_ce) as (SameSide_l_m_ce & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_m_c) as neq_c_m.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_b_m_c) as BetS_c_m_b.

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_c_m_b neq_c_m) as OnRay_cm_b.

	assert (eq c c) as eq_c_c by (reflexivity).
	pose proof (by_def_Col_from_eq_A_B c c e eq_c_c) as Col_c_c_e.
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_l_m_ce Col_c_c_e OnRay_cm_b) as SameSide_l_b_ce.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_l_b_ce) as (SameSide_b_l_ce & _ & _).

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_e_l_d neq_e_l) as OnRay_el_d.

	assert (eq e e) as eq_e_e by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C c e e eq_e_e) as Col_c_e_e.
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_b_l_ce Col_c_e_e OnRay_el_d) as SameSide_b_d_ce.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_b_d_ce) as (SameSide_d_b_ce & _ & _).

	assert (Par_bc_de_2 := Par_bc_de).
	destruct Par_bc_de_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_b_c_d_e & _ & _).

	assert (~ Cross b d c e) as n_Cross_bd_ce.
	{
		intro Cross_bd_ce.

		assert (~ Col b c e) as n_Col_b_c_e.
		{
			intro Col_b_c_e.
			pose proof (by_def_Col_from_eq_B_C d e e eq_e_e) as Col_d_e_e.
			pose proof (by_def_Meet _ _ _ _ _ neq_b_c neq_d_e Col_b_c_e Col_d_e_e) as Meet_b_c_d_e.
			contradict Meet_b_c_d_e.
			exact n_Meet_b_c_d_e.
		}
		pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_b_c_e) as nCol_b_c_e.

		pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_bd_ce nCol_b_c_e) as (OppositeSide_b_ce_d & _ & _ & _).
		pose proof (by_prop_SameSide_not_OppositeSide _ _ _ _ SameSide_b_d_ce) as n_OppositeSide_b_ce_d.
		contradict OppositeSide_b_ce_d.
		exact n_OppositeSide_b_ce_d.
	}

	pose proof (lemma_crisscross _ _ _ _ Par_bc_de n_Cross_bd_ce) as Cross_be_dc.

	destruct Cross_be_dc as (t & BetS_b_t_e & BetS_d_t_c).
	pose proof (cn_sumofparts_Quad_Tri_sharedside _ _ _ _ _ _ _ _ _ _ _ _ BetS_D_L_E BetS_d_l_e EqAreaTri_LEC_lec EqAreaQuad_BDLC_bdlc BetS_B_T_E BetS_D_T_C BetS_b_t_e BetS_d_t_c) as EqAreaQuad_BDEC_bdec.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_BDEC_bdec) as (_ & _ & _ & _ & _ & _ & EqAreaQuad_BDEC_bced).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_BDEC_bced) as EqAreaQuad_bced_BDEC.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_bced_BDEC) as (_ & _ & _ & _ & _ & _ & EqAreaQuad_bced_BCED).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_bced_BCED) as EqAreaQuad_BCED_bced.

	exact EqAreaQuad_BCED_bced.
Qed.

End Euclid.
