Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E .
Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col .
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Cross.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_Par.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_def_Rectangle.
Require Import ProofCheckingEuclid.by_def_SameSide.
Require Import ProofCheckingEuclid.by_def_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_OnRay_assert.
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
	intros EqAreaQuad_B_M_L_D_b_m_l_d.
	intros EqAreaQuad_M_C_E_L_m_c_e_l.
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
	destruct Parallelogram_M_C_E_L_2 as (Par_M_C_E_L & Par_M_L_C_E).
	pose proof (by_prop_Par_NC _ _ _ _ Par_M_C_E_L) as (_ & _ & _ & nCol_M_C_L).
	assert (Parallelogram_m_c_e_l_2 := Parallelogram_m_c_e_l).
	destruct Parallelogram_m_c_e_l_2 as (Par_m_c_e_l & Par_m_l_c_e).
	pose proof (by_prop_Par_NC _ _ _ _ Par_m_c_e_l) as (_ & _ & _ & nCol_m_c_l).
	pose proof (proposition_34 _ _ _ _ Parallelogram_M_C_E_L) as (_ & _ & _ & _ & CongTriangles_C_M_L_L_E_C).
	pose proof (proposition_34 _ _ _ _ Parallelogram_m_c_e_l) as (_ & _ & _ & _ & CongTriangles_c_m_l_l_e_c).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_C_M_L_L_E_C) as EqAreaTri_C_M_L_L_E_C.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_c_m_l_l_e_c) as EqAreaTri_c_m_l_l_e_c.

	destruct Rectangle_M_C_E_L as (_ & _ & _ & _ & Cross_M_E_C_L).
	destruct Rectangle_m_c_e_l as (_ & _ & _ & _ & Cross_m_e_c_l).
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_c_m_l_l_e_c) as (_ & _ & _ & _ & EqAreaTri_c_m_l_c_l_e).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_c_m_l_c_l_e) as EqAreaTri_c_l_e_c_m_l.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_c_l_e_c_m_l) as (_ & _ & EqAreaTri_c_l_e_m_c_l & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_c_l_e_m_c_l) as EqAreaTri_m_c_l_c_l_e.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_C_M_L_L_E_C) as (_ & _ & _ & _ & EqAreaTri_C_M_L_C_L_E).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_C_M_L_C_L_E) as EqAreaTri_C_L_E_C_M_L.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_C_L_E_C_M_L) as (_ & _ & EqAreaTri_C_L_E_M_C_L & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_C_L_E_M_C_L) as EqAreaTri_M_C_L_C_L_E.
	pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_M_E_C_L nCol_M_C_L) as (OppositeSide_M_C_L_E & _ & _ & _).
	pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_m_e_c_l nCol_m_c_l) as (OppositeSide_m_c_l_e & _ & _ & _).
	pose proof (axiom_halvesofequals _ _ _ _ _ _ _ _ EqAreaTri_M_C_L_C_L_E OppositeSide_M_C_L_E EqAreaTri_m_c_l_c_l_e OppositeSide_m_c_l_e EqAreaQuad_M_C_E_L_m_c_e_l) as EqAreaTri_M_C_L_m_c_l.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_M_C_E_L_m_c_e_l) as (_ & _ & _ & _ & _ & EqAreaQuad_M_C_E_L_e_c_m_l & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_M_C_E_L_e_c_m_l) as EqAreaQuad_e_c_m_l_M_C_E_L.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_e_c_m_l_M_C_E_L) as (_ & _ & _ & _ & _ & EqAreaQuad_e_c_m_l_E_C_M_L & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_e_c_m_l_E_C_M_L) as EqAreaQuad_E_C_M_L_e_c_m_l.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_M_C_L_E) as OppositeSide_E_C_L_M.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_m_c_l_e) as OppositeSide_e_c_l_m.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_M_C_L_C_L_E) as (_ & _ & _ & _ & EqAreaTri_M_C_L_E_C_L).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_M_C_L_E_C_L) as EqAreaTri_E_C_L_M_C_L.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_E_C_L_M_C_L) as (EqAreaTri_E_C_L_C_L_M & _ & _ & _ & _).
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_m_c_l_c_l_e) as (_ & _ & _ & _ & EqAreaTri_m_c_l_e_c_l).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_m_c_l_e_c_l) as EqAreaTri_e_c_l_m_c_l.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_e_c_l_m_c_l) as (EqAreaTri_e_c_l_c_l_m & _ & _ & _ & _).
	pose proof (axiom_halvesofequals _ _ _ _ _ _ _ _ EqAreaTri_E_C_L_C_L_M OppositeSide_E_C_L_M EqAreaTri_e_c_l_c_l_m OppositeSide_e_c_l_m EqAreaQuad_E_C_M_L_e_c_m_l) as EqAreaTri_E_C_L_e_c_l.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_B_M_L_D_b_m_l_d) as (_ & _ & _ & _ & EqAreaQuad_B_M_L_D_d_b_m_l & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_B_M_L_D_d_b_m_l) as EqAreaQuad_d_b_m_l_B_M_L_D.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_d_b_m_l_B_M_L_D) as (_ & _ & _ & _ & EqAreaQuad_d_b_m_l_D_B_M_L & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_d_b_m_l_D_B_M_L) as EqAreaQuad_D_B_M_L_d_b_m_l.
	pose proof (by_def_Col_from_BetS_A_B_C B M C BetS_B_M_C) as Col_B_M_C.
	pose proof (by_prop_Col_order _ _ _ Col_B_M_C) as (_ & Col_M_C_B & _ & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_M_C) as (_ & _ & neq_B_C).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_M_C_E_L) as Par_E_L_M_C.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_E_L_M_C Col_M_C_B neq_B_C) as Par_E_L_B_C.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_E_L_B_C) as Par_B_C_E_L.
	pose proof (by_def_Col_from_BetS_A_B_C E L D BetS_E_L_D) as Col_E_L_D.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_L_D) as (neq_L_D & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_L_D) as neq_D_L.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_B_C_E_L Col_E_L_D neq_D_L) as Par_B_C_D_L.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_L_D) as (_ & neq_E_L & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_M_C) as (neq_M_C & _ & _).
	
	assert (Par_E_L_M_C_2 := Par_E_L_M_C).
	destruct Par_E_L_M_C_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_E_L_M_C & _ & _).

	assert (~ Cross B D C L) as n_Cross_B_D_C_L.
	{
		intro Cross_B_D_C_L.

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
		pose proof (by_def_Col_from_BetS_A_C_B C L P BetS_C_P_L) as Col_C_L_P.
		epose proof (by_def_SameSide D M C L E L P Col_C_L_L Col_C_L_P BetS_D_L_E BetS_M_P_E nCol_C_L_D nCol_C_L_M) as SameSide_D_M_C_L.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_C) as BetS_C_M_B.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_C_M_B) as (_ & neq_C_M & _).
		
		pose proof (by_def_OnRay_from_BetS_A_B_E C M B BetS_C_M_B neq_C_M) as OnRay_C_M_B.

		assert (eq C C) as eq_C_C by (reflexivity).
		pose proof (by_def_Col_from_eq_A_B C C L eq_C_C) as Col_C_C_L.
		pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_D_M_C_L Col_C_C_L OnRay_C_M_B) as SameSide_D_B_C_L.
		pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_D_B_C_L) as (SameSide_B_D_C_L & _ & _).
		pose proof (by_prop_SameSide_not_OppositeSide _ _ _ _ SameSide_B_D_C_L) as n_OppositeSide_B_C_L_D.

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

		pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_B_D_C_L nCol_B_C_L) as (OppositeSide_B_C_L_D & _ & _ & _).
		contradict OppositeSide_B_C_L_D.
		exact n_OppositeSide_B_C_L_D.
	}

	pose proof (lemma_crisscross _ _ _ _ Par_B_C_D_L n_Cross_B_D_C_L) as Cross_B_L_D_C.

	destruct Cross_B_L_D_C as (R & BetS_B_R_L & BetS_D_R_C).
	pose proof (by_def_Col_from_BetS_A_B_C b m c BetS_b_m_c) as Col_b_m_c.
	pose proof (by_prop_Col_order _ _ _ Col_b_m_c) as (_ & Col_m_c_b & _ & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_b_m_c) as (_ & _ & neq_b_c).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_m_c_e_l) as Par_e_l_m_c.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_e_l_m_c Col_m_c_b neq_b_c) as Par_e_l_b_c.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_e_l_b_c) as Par_b_c_e_l.
	pose proof (by_def_Col_from_BetS_A_B_C e l d BetS_e_l_d) as Col_e_l_d.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_e_l_d) as (neq_l_d & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_l_d) as neq_d_l.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_b_c_e_l Col_e_l_d neq_d_l) as Par_b_c_d_l.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_e_l_d) as (_ & neq_e_l & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_b_m_c) as (neq_m_c & _ & _).
	
	assert (Par_e_l_m_c_2 := Par_e_l_m_c).
	destruct Par_e_l_m_c_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_e_l_m_c & _ & _).

	assert (~ Cross b d c l) as n_Cross_b_d_c_l.
	{
		intro Cross_b_d_c_l.

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
		pose proof (by_def_Col_from_BetS_A_C_B c l p BetS_c_p_l) as Col_c_l_p.
		epose proof (by_def_SameSide d m c l e l p Col_c_l_l Col_c_l_p BetS_d_l_e BetS_m_p_e nCol_c_l_d nCol_c_l_m) as SameSide_d_m_c_l.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_b_m_c) as BetS_c_m_b.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_c_m_b) as (_ & neq_c_m & _).
		
		pose proof (by_def_OnRay_from_BetS_A_B_E c m b BetS_c_m_b neq_c_m) as OnRay_c_m_b.

		assert (eq c c) as eq_c_c by (reflexivity).
		pose proof (by_def_Col_from_eq_A_B c c l eq_c_c) as Col_c_c_l.
		pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_d_m_c_l Col_c_c_l OnRay_c_m_b) as SameSide_d_b_c_l.
		pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_d_b_c_l) as (SameSide_b_d_c_l & _ & _).
		pose proof (by_prop_SameSide_not_OppositeSide _ _ _ _ SameSide_b_d_c_l) as n_OppositeSide_b_c_l_d.

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

		pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_b_d_c_l nCol_b_c_l) as (OppositeSide_b_c_l_d & _ & _ & _).
		contradict OppositeSide_b_c_l_d.
		exact n_OppositeSide_b_c_l_d.
	}

	pose proof (lemma_crisscross _ _ _ _ Par_b_c_d_l n_Cross_b_d_c_l) as Cross_b_l_d_c.

	destruct Cross_b_l_d_c as (r & BetS_b_r_l & BetS_d_r_c).
	pose proof (axiom_paste2 _ _ _ _ _ _ _ _ _ _ _ _ BetS_B_M_C BetS_b_m_c EqAreaTri_M_C_L_m_c_l EqAreaQuad_D_B_M_L_d_b_m_l BetS_D_R_C BetS_B_R_L BetS_d_r_c BetS_b_r_l) as EqAreaQuad_D_B_C_L_d_b_c_l.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_D_B_C_L_d_b_c_l) as (_ & _ & _ & EqAreaQuad_D_B_C_L_b_d_l_c & _ & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_D_B_C_L_b_d_l_c) as EqAreaQuad_b_d_l_c_D_B_C_L.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_b_d_l_c_D_B_C_L) as (_ & _ & _ & EqAreaQuad_b_d_l_c_B_D_L_C & _ & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_b_d_l_c_B_D_L_C) as EqAreaQuad_B_D_L_C_b_d_l_c.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_E_C_L_e_c_l) as (_ & _ & _ & _ & EqAreaTri_E_C_L_l_e_c).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_E_C_L_l_e_c) as EqAreaTri_l_e_c_E_C_L.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_l_e_c_E_C_L) as (_ & _ & _ & _ & EqAreaTri_l_e_c_L_E_C).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_l_e_c_L_E_C) as EqAreaTri_L_E_C_l_e_c.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_L_D) as BetS_D_L_E.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_e_l_d) as BetS_d_l_e.
	pose proof (by_prop_Par_flip _ _ _ _ Par_B_C_E_L) as (_ & Par_B_C_L_E & _).
	pose proof (by_prop_Col_order _ _ _ Col_E_L_D) as (Col_L_E_D & _ & _ & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_L_D) as (_ & _ & neq_E_D).
	pose proof (by_prop_neq_symmetric _ _ neq_E_D) as neq_D_E.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_B_C_L_E Col_L_E_D neq_D_E) as Par_B_C_D_E.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_M_L_C_E) as Par_C_E_M_L.
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_C_E_M_L) as TarskiPar_C_E_M_L.

	assert (TarskiPar_C_E_M_L_2 := TarskiPar_C_E_M_L).
	destruct TarskiPar_C_E_M_L_2 as (neq_C_E & neq_M_L & n_Meet_C_E_M_L & SameSide_M_L_C_E).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_M_L_C_E) as (SameSide_L_M_C_E & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_M_C) as neq_C_M.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_C) as BetS_C_M_B.
	
	pose proof (by_def_OnRay_from_BetS_A_B_E C M B BetS_C_M_B neq_C_M) as OnRay_C_M_B.

	assert (eq C C) as eq_C_C by (reflexivity).
	pose proof (by_def_Col_from_eq_A_B C C E eq_C_C) as Col_C_C_E.
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_L_M_C_E Col_C_C_E OnRay_C_M_B) as SameSide_L_B_C_E.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_L_B_C_E) as (SameSide_B_L_C_E & _ & _).
	
	pose proof (by_def_OnRay_from_BetS_A_B_E E L D BetS_E_L_D neq_E_L) as OnRay_E_L_D.

	assert (eq E E) as eq_E_E by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C C E E eq_E_E) as Col_C_E_E.
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_B_L_C_E Col_C_E_E OnRay_E_L_D) as SameSide_B_D_C_E.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_B_D_C_E) as (SameSide_D_B_C_E & _ & _).
	
	assert (Par_B_C_D_E_2 := Par_B_C_D_E).
	destruct Par_B_C_D_E_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_B_C_D_E & _ & _).

	assert (~ Cross B D C E) as n_Cross_B_D_C_E.
	{
		intro Cross_B_D_C_E.

		assert (~ Col B C E) as n_Col_B_C_E.
		{
			intro Col_B_C_E.
			pose proof (by_def_Col_from_eq_B_C D E E eq_E_E) as Col_D_E_E.
			pose proof (by_def_Meet _ _ _ _ _ neq_B_C neq_D_E Col_B_C_E Col_D_E_E) as Meet_B_C_D_E.
			contradict Meet_B_C_D_E.
			exact n_Meet_B_C_D_E.
		}
		pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_B_C_E) as nCol_B_C_E.

		pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_B_D_C_E nCol_B_C_E) as (OppositeSide_B_C_E_D & _ & _ & _).
		pose proof (by_prop_SameSide_not_OppositeSide _ _ _ _ SameSide_B_D_C_E) as n_OppositeSide_B_C_E_D.
		contradict OppositeSide_B_C_E_D.
		exact n_OppositeSide_B_C_E_D.
	}

	pose proof (lemma_crisscross _ _ _ _ Par_B_C_D_E n_Cross_B_D_C_E) as Cross_B_E_D_C.

	destruct Cross_B_E_D_C as (T & BetS_B_T_E & BetS_D_T_C).
	pose proof (by_prop_Par_flip _ _ _ _ Par_b_c_e_l) as (_ & Par_b_c_l_e & _).
	pose proof (by_prop_Col_order _ _ _ Col_e_l_d) as (Col_l_e_d & _ & _ & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_e_l_d) as (_ & _ & neq_e_d).
	pose proof (by_prop_neq_symmetric _ _ neq_e_d) as neq_d_e.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_b_c_l_e Col_l_e_d neq_d_e) as Par_b_c_d_e.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_m_l_c_e) as Par_c_e_m_l.
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_c_e_m_l) as TarskiPar_c_e_m_l.

	assert (TarskiPar_c_e_m_l_2 := TarskiPar_c_e_m_l).
	destruct TarskiPar_c_e_m_l_2 as (neq_c_e & neq_m_l & n_Meet_c_e_m_l & SameSide_m_l_c_e).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_m_l_c_e) as (SameSide_l_m_c_e & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_m_c) as neq_c_m.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_b_m_c) as BetS_c_m_b.
	
	pose proof (by_def_OnRay_from_BetS_A_B_E c m b BetS_c_m_b neq_c_m) as OnRay_c_m_b.

	assert (eq c c) as eq_c_c by (reflexivity).
	pose proof (by_def_Col_from_eq_A_B c c e eq_c_c) as Col_c_c_e.
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_l_m_c_e Col_c_c_e OnRay_c_m_b) as SameSide_l_b_c_e.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_l_b_c_e) as (SameSide_b_l_c_e & _ & _).
	
	pose proof (by_def_OnRay_from_BetS_A_B_E e l d BetS_e_l_d neq_e_l) as OnRay_e_l_d.

	assert (eq e e) as eq_e_e by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C c e e eq_e_e) as Col_c_e_e.
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_b_l_c_e Col_c_e_e OnRay_e_l_d) as SameSide_b_d_c_e.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_b_d_c_e) as (SameSide_d_b_c_e & _ & _).
	
	assert (Par_b_c_d_e_2 := Par_b_c_d_e).
	destruct Par_b_c_d_e_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_b_c_d_e & _ & _).

	assert (~ Cross b d c e) as n_Cross_b_d_c_e.
	{
		intro Cross_b_d_c_e.

		assert (~ Col b c e) as n_Col_b_c_e.
		{
			intro Col_b_c_e.
			pose proof (by_def_Col_from_eq_B_C d e e eq_e_e) as Col_d_e_e.
			pose proof (by_def_Meet _ _ _ _ _ neq_b_c neq_d_e Col_b_c_e Col_d_e_e) as Meet_b_c_d_e.
			contradict Meet_b_c_d_e.
			exact n_Meet_b_c_d_e.
		}
		pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_b_c_e) as nCol_b_c_e.

		pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_b_d_c_e nCol_b_c_e) as (OppositeSide_b_c_e_d & _ & _ & _).
		pose proof (by_prop_SameSide_not_OppositeSide _ _ _ _ SameSide_b_d_c_e) as n_OppositeSide_b_c_e_d.
		contradict OppositeSide_b_c_e_d.
		exact n_OppositeSide_b_c_e_d.
	}

	pose proof (lemma_crisscross _ _ _ _ Par_b_c_d_e n_Cross_b_d_c_e) as Cross_b_e_d_c.

	destruct Cross_b_e_d_c as (t & BetS_b_t_e & BetS_d_t_c).
	pose proof (axiom_paste2 _ _ _ _ _ _ _ _ _ _ _ _ BetS_D_L_E BetS_d_l_e EqAreaTri_L_E_C_l_e_c EqAreaQuad_B_D_L_C_b_d_l_c BetS_B_T_E BetS_D_T_C BetS_b_t_e BetS_d_t_c) as EqAreaQuad_B_D_E_C_b_d_e_c.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_B_D_E_C_b_d_e_c) as (_ & _ & _ & _ & _ & _ & EqAreaQuad_B_D_E_C_b_c_e_d).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_B_D_E_C_b_c_e_d) as EqAreaQuad_b_c_e_d_B_D_E_C.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_b_c_e_d_B_D_E_C) as (_ & _ & _ & _ & _ & _ & EqAreaQuad_b_c_e_d_B_C_E_D).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_b_c_e_d_B_C_E_D) as EqAreaQuad_B_C_E_D_b_c_e_d.

	exact EqAreaQuad_B_C_E_D_b_c_e_d.
Qed.

End Euclid.
