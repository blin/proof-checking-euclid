Require Import ProofCheckingEuclid.by_def_AngleSum.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_CongTriangles.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_Par.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_AngleSum_respects_congruence.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_flip.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_flip.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Euclid4.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_diagonalsbisect.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_righttogether.
Require Import ProofCheckingEuclid.lemma_squareparallelogram.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_34.
Require Import ProofCheckingEuclid.proposition_41.
Require Import ProofCheckingEuclid.proposition_47A.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_47B :
	forall A B C D E F G,
	Triangle A B C ->
	RightTriangle B A C ->
	Square A B F G ->
	OppositeSide G B A C ->
	Square B C E D ->
	OppositeSide D C B A ->
	exists X Y, (
		Parallelogram B X Y D /\
		BetS B X C /\
		Parallelogram X C E Y /\
		BetS D Y E /\
		BetS Y X A /\
		RightTriangle D Y A /\
		EqAreaQuad A B F G B X Y D
	).
Proof.
	intros A B C D E F G.
	intros Triangle_ABC.
	intros RightTriangle_BAC.
	intros Square_A_B_F_G.
	intros OppositeSide_G_BA_C.
	intros Square_B_C_E_D.
	intros OppositeSide_D_CB_A.

	assert (eq B B) as eq_B_B by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C F B B eq_B_B) as Col_F_B_B.
	pose proof (by_def_Col_from_eq_B_C D B B eq_B_B) as Col_D_B_B.

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_ABC) as nCol_A_B_C.

	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).

	pose proof (by_prop_CongA_reflexive _ _ _ nCol_A_B_C) as CongA_ABC_ABC.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_B_C) as CongA_ABC_CBA.
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_C_B_A) as CongA_CBA_CBA.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_A) as OnRay_BA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_C) as OnRay_BC_C.

	pose proof (lemma_squareparallelogram _ _ _ _ Square_A_B_F_G) as Parallelogram_A_B_F_G.
	pose proof (by_prop_Parallelogram_flip _ _ _ _ Parallelogram_A_B_F_G) as Parallelogram_B_A_G_F.

	pose proof (proposition_34 _ _ _ _ Parallelogram_B_A_G_F) as (_ & _ & _ & _ & CongTriangles_ABF_FGA).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_ABF_FGA) as EqAreaTri_A_B_F_F_G_A.
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_A_B_F_F_G_A) as EqAreaTri_F_G_A_A_B_F.

	assert (Parallelogram_A_B_F_G_2 := Parallelogram_A_B_F_G).
	destruct Parallelogram_A_B_F_G_2 as (Par_AB_FG & Par_AG_BF).

	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_FG) as (_ & Par_AB_GF & _).
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_AB_GF) as TarskiPar_AB_GF.
	assert (TarskiPar_AB_GF_2 := TarskiPar_AB_GF).
	destruct TarskiPar_AB_GF_2 as (_ & _ & _ & SameSide_G_F_AB).
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_G_F_AB) as (SameSide_F_G_AB & _ & _).

	pose proof (by_prop_Par_flip _ _ _ _ Par_AG_BF) as (_ & Par_AG_FB & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AG_FB) as Par_FB_AG.

	assert (Square_A_B_F_G_2 := Square_A_B_F_G).
	destruct Square_A_B_F_G_2 as (
		_ & Cong_AB_BF & _ & RightTriangle_GAB & RightTriangle_ABF & _ & _
	).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_BF) as (Cong_BA_FB & Cong_BA_BF & Cong_AB_FB).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AB_BF) as Cong_BF_AB.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BF_AB) as (Cong_FB_BA & Cong_FB_AB & Cong_BF_BA).

	pose proof (lemma_righttogether _ _ _ _ RightTriangle_GAB RightTriangle_BAC OppositeSide_G_BA_C) as (_ & BetS_G_A_C).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_A_C) as BetS_C_A_G.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_G_A_C) as (_ & neq_G_A & neq_G_C).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_A_G) as (neq_A_G & _ & neq_C_G).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_G_A_C) as Col_G_A_C.
	pose proof (by_prop_Col_order _ _ _ Col_G_A_C) as (Col_A_G_C & Col_A_C_G & Col_C_G_A & Col_G_C_A & Col_C_A_G).

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_FB_AG Col_A_G_C neq_C_G) as Par_FB_CG.
	pose proof (by_prop_Par_flip _ _ _ _ Par_FB_CG) as (_ & Par_FB_GC & _).

	assert (Par_FB_GC_2 := Par_FB_GC).
	destruct Par_FB_GC_2 as (_ & _ & _ & _ & _ & neq_F_B & _ & _ & _ & _ & _ & _ & _ & n_Meet_F_B_G_C & _ & _).

	pose proof (by_prop_neq_symmetric _ _ neq_F_B) as neq_B_F.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_F) as OnRay_BF_F.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_ABF) as RightTriangle_FBA.

	pose proof (by_prop_OppositeSide_flip _ _ _ _ OppositeSide_G_BA_C) as OppositeSide_G_AB_C.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_F_G_AB OppositeSide_G_AB_C) as OppositeSide_F_AB_C.

	pose proof (lemma_squareparallelogram _ _ _ _ Square_B_C_E_D) as Parallelogram_B_C_E_D.

	assert (Parallelogram_B_C_E_D_2 := Parallelogram_B_C_E_D).
	destruct Parallelogram_B_C_E_D_2 as (_ & Par_BD_CE).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_BD_CE) as Par_CE_BD.
	pose proof (by_prop_Par_flip _ _ _ _ Par_CE_BD) as (_ & Par_CE_DB & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_CE_DB) as (_ & nCol_C_D_B & _ & _).

	pose proof (by_prop_nCol_order _ _ _ nCol_C_D_B) as (nCol_D_C_B & nCol_D_B_C & nCol_B_C_D & nCol_C_B_D & nCol_B_D_C).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_C_D_B) as (neq_C_D & neq_D_B & _ & neq_D_C & neq_B_D & _).

	pose proof (by_prop_CongA_reflexive _ _ _ nCol_D_B_C) as CongA_DBC_DBC.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_D) as OnRay_BD_D.

	assert (Square_B_C_E_D_2 := Square_B_C_E_D).
	destruct Square_B_C_E_D_2 as (
		_ & _ & Cong_BC_DB & RightTriangle_DBC & _ & _ &_
	).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BC_DB) as Cong_DB_BC.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_DB_BC) as (_ & Cong_BD_BC & _).

	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_FBA RightTriangle_DBC) as CongA_FBA_DBC.

	pose proof (proposition_47A _ _ _ _ _ Triangle_ABC RightTriangle_BAC Square_B_C_E_D OppositeSide_D_CB_A) as (
		M & L & Parallelogram_B_M_L_D & BetS_B_M_C & Parallelogram_M_C_E_L & BetS_D_L_E & BetS_L_M_A & RightTriangle_DLA
	).

	pose proof (proposition_34 _ _ _ _ Parallelogram_B_M_L_D) as (_ & _ & _ & _ & CongTriangles_MBD_DLM).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_MBD_DLM) as EqAreaTri_M_B_D_D_L_M.

	assert (Parallelogram_B_M_L_D_2 := Parallelogram_B_M_L_D).
	destruct Parallelogram_B_M_L_D_2 as (Par_BM_LD & Par_BD_ML).
	pose proof (by_prop_Par_flip _ _ _ _ Par_BM_LD) as (_ & _ & Par_MB_DL).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_BD_ML) as Par_ML_BD.
	pose proof (by_def_Parallelogram _ _ _ _ Par_MB_DL Par_ML_BD) as Parallelogram_M_B_D_L.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_M_C) as Col_B_M_C.
	pose proof (by_prop_Col_order _ _ _ Col_B_M_C) as (_ & _ & Col_C_B_M & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_L_M_A) as BetS_A_M_L.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_L_M_A) as (neq_M_A & neq_L_M & neq_L_A).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_M_L) as (neq_M_L & neq_A_M & neq_A_L).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_L_M_A) as Col_L_M_A.
	pose proof (by_prop_Col_order _ _ _ Col_L_M_A) as (Col_M_L_A & Col_M_A_L & Col_A_L_M & Col_L_A_M & Col_A_M_L).

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_BD_ML Col_M_L_A neq_A_L) as Par_BD_AL.
	pose proof (by_prop_Par_flip _ _ _ _ Par_BD_AL) as (_ & _ & Par_DB_LA).
	assert (Par_DB_LA_2 := Par_DB_LA).
	destruct Par_DB_LA_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_D_B_L_A & _ & _).

	destruct OppositeSide_F_AB_C as (a & BetS_F_a_C & Col_A_B_a & nCol_A_B_F).

	pose proof (by_prop_Col_order _ _ _ Col_A_B_a) as (Col_B_A_a & _ & _ & _ & _).

	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_F) as (_ & _ & _ & _ & nCol_F_B_A).
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_F_B_A) as CongA_FBA_FBA.

	pose proof (
		lemma_collinearbetween _ _ _ _ _ _ _ Col_F_B_B Col_G_A_C neq_F_B neq_G_C neq_F_B neq_A_C n_Meet_F_B_G_C BetS_F_a_C Col_B_A_a
	) as BetS_B_a_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_a_A) as (_ & neq_B_a & _).
	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_a_A neq_B_a) as OnRay_Ba_A.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_Ba_A) as OnRay_BA_a.

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_FBA_FBA OnRay_BF_F OnRay_BA_a) as CongA_FBA_FBa.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_ABC_ABC OnRay_BA_a OnRay_BC_C) as CongA_ABC_aBC.
	pose proof (by_def_AngleSum _ _ _ _ _ _ _ _ _ _ CongA_FBA_FBa CongA_ABC_aBC BetS_F_a_C) as AngleSum_FBA_ABC_FBC.

	assert (OppositeSide_D_CB_A_2 := OppositeSide_D_CB_A).
	destruct OppositeSide_D_CB_A_2 as (c & BetS_D_c_A & Col_C_B_c &_ ).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_D_c_A) as Col_D_c_A.
	pose proof (by_prop_Col_order _ _ _ Col_D_c_A) as (Col_c_D_A & _ & _ & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_D_c_A) as (_ & neq_D_c & _).
	pose proof (by_prop_neq_symmetric _ _ neq_D_c) as neq_c_D.

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_B_M Col_C_B_c neq_C_B) as Col_B_M_c.

	pose proof (
		lemma_collinearbetween _ _ _ _ _ _ _ Col_D_B_B Col_L_M_A neq_D_B neq_L_A neq_D_B neq_M_A n_Meet_D_B_L_A BetS_D_c_A Col_B_M_c
	) as BetS_B_c_M.

	pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_B_c_M BetS_B_M_C) as BetS_B_c_C.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_c_C) as (neq_c_C & neq_B_c & _).
	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_c_C neq_B_c) as OnRay_Bc_C.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_Bc_C) as OnRay_BC_c.

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_CBA_CBA OnRay_BC_c OnRay_BA_A) as CongA_CBA_cBA.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_DBC_DBC OnRay_BD_D OnRay_BC_c) as CongA_DBC_DBc.
	pose proof (by_def_AngleSum _ _ _ _ _ _ _ _ _ _ CongA_DBC_DBc CongA_CBA_cBA BetS_D_c_A) as AngleSum_DBC_CBA_DBA.

	pose proof (
		by_prop_AngleSum_respects_congruence
		_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
		AngleSum_FBA_ABC_FBC CongA_FBA_DBC CongA_ABC_CBA AngleSum_DBC_CBA_DBA
	) as CongA_FBC_DBA.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_FBC_DBA) as CongA_DBA_FBC.

	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_DBA_FBC) as nCol_F_B_C.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_F_B_C) as CongA_FBC_CBF.

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_DBA_FBC CongA_FBC_CBF) as CongA_DBA_CBF.

	pose proof (proposition_04 _ _ _ _ _ _ Cong_BD_BC Cong_BA_BF CongA_DBA_CBF) as (
		Cong_DA_CF & _ & _
	).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_DA_CF) as (Cong_AD_FC & _ & _).
	pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_AB_FB Cong_BD_BC Cong_AD_FC) as CongTriangles_ABD_FBC.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_ABD_FBC) as EqAreaTri_A_B_D_F_B_C.
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_A_B_D_F_B_C) as EqAreaTri_F_B_C_A_B_D.

	pose proof (proposition_41 _ _ _ _ _ Parallelogram_M_B_D_L Col_M_L_A) as EqAreaTri_M_B_D_A_B_D.
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_M_B_D_A_B_D) as EqAreaTri_A_B_D_M_B_D.

	pose proof (proposition_41 _ _ _ _ _ Parallelogram_A_B_F_G Col_A_G_C) as EqAreaTri_A_B_F_C_B_F.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_A_B_F_C_B_F) as (_ & _ & _ & EqAreaTri_A_B_F_F_B_C & _).

	pose proof (axiom_EqAreaTri_transitive _ _ _ _ _ _ _ _ _ EqAreaTri_A_B_F_F_B_C EqAreaTri_F_B_C_A_B_D) as EqAreaTri_A_B_F_A_B_D.
	pose proof (axiom_EqAreaTri_transitive _ _ _ _ _ _ _ _ _ EqAreaTri_A_B_F_A_B_D EqAreaTri_A_B_D_M_B_D) as EqAreaTri_A_B_F_M_B_D.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_A_B_F_M_B_D) as (_ & _ & _ & _ & EqAreaTri_A_B_F_D_M_B).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_A_B_F_D_M_B) as EqAreaTri_D_M_B_A_B_F.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_D_M_B_A_B_F) as (_ & _ & _ & _ & EqAreaTri_D_M_B_F_A_B).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_D_M_B_F_A_B) as EqAreaTri_F_A_B_D_M_B.

	pose proof (axiom_EqAreaTri_transitive _ _ _ _ _ _ _ _ _ EqAreaTri_F_G_A_A_B_F EqAreaTri_A_B_F_M_B_D) as EqAreaTri_F_G_A_M_B_D.
	pose proof (axiom_EqAreaTri_transitive _ _ _ _ _ _ _ _ _ EqAreaTri_F_G_A_M_B_D EqAreaTri_M_B_D_D_L_M) as EqAreaTri_F_G_A_D_L_M.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_F_G_A_D_L_M) as (_ & EqAreaTri_F_G_A_D_M_L & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_F_G_A_D_M_L) as EqAreaTri_D_M_L_F_G_A.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_D_M_L_F_G_A) as (_ & EqAreaTri_D_M_L_F_A_G & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_D_M_L_F_A_G) as EqAreaTri_F_A_G_D_M_L.

	pose proof (lemma_diagonalsbisect _ _ _ _ Parallelogram_A_B_F_G) as (m & Midpoint_A_m_F & Midpoint_B_m_G).

	assert (Midpoint_A_m_F_2 := Midpoint_A_m_F).
	destruct Midpoint_A_m_F_2 as (BetS_A_m_F & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_m_F) as BetS_F_m_A.

	assert (Midpoint_B_m_G_2 := Midpoint_B_m_G).
	destruct Midpoint_B_m_G_2 as (BetS_B_m_G & _).

	pose proof (lemma_diagonalsbisect _ _ _ _ Parallelogram_B_M_L_D) as (n & Midpoint_B_n_L & Midpoint_M_n_D).

	assert (Midpoint_B_n_L_2 := Midpoint_B_n_L).
	destruct Midpoint_B_n_L_2 as (BetS_B_n_L & _).

	assert (Midpoint_M_n_D_2 := Midpoint_M_n_D).
	destruct Midpoint_M_n_D_2 as (BetS_M_n_D & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_M_n_D) as BetS_D_n_M.

	assert (BetS F m A \/ eq F m \/ eq m A) as BetS_F_m_A' by (left; exact BetS_F_m_A).
	assert (BetS D n M \/ eq D n \/ eq n M) as BetS_D_n_M' by (left; exact BetS_D_n_M).

	pose proof (
		axiom_paste3
		F A B G m
		D M B L n
		EqAreaTri_F_A_B_D_M_B
		EqAreaTri_F_A_G_D_M_L
		BetS_B_m_G
		BetS_F_m_A'
		BetS_B_n_L
		BetS_D_n_M'
	) as EqAreaQuad_F_B_A_G_D_B_M_L.

	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_F_B_A_G_D_B_M_L) as (
		EqAreaQuad_F_B_A_G_B_M_L_D & _ & _ & _ & _ & _ & _
	).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_F_B_A_G_B_M_L_D) as EqAreaQuad_B_M_L_D_F_B_A_G.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_B_M_L_D_F_B_A_G) as (
		_ & _ & _ & _ & _ & EqAreaQuad_B_M_L_D_A_B_F_G & _
	).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_B_M_L_D_A_B_F_G) as EqAreaQuad_A_B_F_G_B_M_L_D.

	exists M, L.
	split.
	exact Parallelogram_B_M_L_D.
	split.
	exact BetS_B_M_C.
	split.
	exact Parallelogram_M_C_E_L.
	split.
	exact BetS_D_L_E.
	split.
	exact BetS_L_M_A.
	split.
	exact RightTriangle_DLA.
	exact EqAreaQuad_A_B_F_G_B_M_L_D.
Qed.

End Euclid.
