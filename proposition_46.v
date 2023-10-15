Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_Square.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_OnRay_impliescollinear.
Require Import ProofCheckingEuclid.by_prop_OnRay_neq_A_B.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_flip.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_symmetric.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_collinear.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_equaltoright.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_oppositeside_onray_PABC_RQP_QABC.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_triangletoparallelogram.
Require Import ProofCheckingEuclid.proposition_11B.
Require Import ProofCheckingEuclid.proposition_31short.
Require Import ProofCheckingEuclid.proposition_34.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_46 :
	forall A B R,
	neq A B ->
	nCol A B R ->
	exists X Y, Square A B X Y /\ OppositeSide Y A B R /\ Parallelogram A B X Y.
Proof.
	intros A B R.
	intros neq_A_B.
	intros nCol_A_B_R.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq B B) as eq_B_B by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C A B A eq_A_A) as Col_A_B_A.
	pose proof (by_def_Col_from_eq_A_C B A B eq_B_B) as Col_B_A_B.
	pose proof (by_def_Col_from_eq_B_C A B B eq_B_B) as Col_A_B_B.

	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_R) as (nCol_B_A_R & nCol_B_R_A & nCol_R_A_B & nCol_A_R_B & nCol_R_B_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_R) as (_ & neq_B_R & neq_A_R & neq_B_A & neq_R_B & neq_R_A).

	pose proof (lemma_extension _ _ _ _ neq_B_A neq_A_B) as (F & BetS_B_A_F & _).

	pose proof (by_def_Col_from_eq_A_C B F B eq_B_B) as Col_B_F_B.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_F) as BetS_F_A_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_A_F) as (neq_A_F & _ & neq_B_F).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_F_A_B) as (_ & neq_F_A & neq_F_B).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_A_F) as Col_B_A_F.
	pose proof (by_prop_Col_order _ _ _ Col_B_A_F) as (Col_A_B_F & Col_A_F_B & Col_F_B_A & Col_B_F_A & Col_F_A_B).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_A_R Col_B_A_B Col_B_A_F neq_B_F) as nCol_B_F_R.

	pose proof (proposition_11B _ _ _ _ BetS_B_A_F nCol_B_F_R) as (C & RightTriangle_BAC & OppositeSide_C_BF_R).

	pose proof (by_def_Col_from_eq_B_C C A A eq_A_A) as Col_C_A_A.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_BAC) as RightTriangle_CAB.

	destruct OppositeSide_C_BF_R as (q & BetS_C_q_R & Col_B_F_q & nCol_B_F_C).

	pose proof (by_prop_Col_order _ _ _ Col_B_F_q) as (Col_F_B_q & _ & _ & _ & _).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_F_B_A Col_F_B_q neq_F_B) as Col_B_A_q.
	pose proof (by_prop_Col_order _ _ _ Col_B_A_q) as (Col_A_B_q & _ & _ & _ & _).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_F_C Col_B_F_A Col_B_F_B neq_A_B) as nCol_A_B_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (_ & neq_B_C & neq_A_C & _ & neq_C_B & neq_C_A).

	pose proof (lemma_layoff _ _ _ _ neq_A_C neq_A_B) as (D & OnRay_AC_D & Cong_AD_AB).

	assert (eq D D) as eq_D_D by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C D A D eq_D_D) as Col_D_A_D.

	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_AC_D) as OnRay_AD_C.
	pose proof (by_prop_OnRay_neq_A_B _ _ _ OnRay_AD_C) as neq_A_D.
	pose proof (by_prop_neq_symmetric _ _ neq_A_D) as neq_D_A.

	pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_AC_D) as Col_A_C_D.
	pose proof (by_prop_Col_order _ _ _ Col_A_C_D) as (Col_C_A_D & _ & _ & _ & _).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AD_AB) as (Cong_DA_BA & Cong_DA_AB & Cong_AD_BA).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AD_AB) as Cong_AB_AD.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_AD) as (Cong_BA_DA & Cong_BA_AD & Cong_AB_DA).

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_CAB Col_C_A_D neq_D_A) as RightTriangle_DAB.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_C_A_B Col_C_A_A Col_C_A_D neq_A_D) as nCol_A_D_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_D_B) as (_ & _ & _ & nCol_A_B_D & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_D_B) as (nCol_D_A_B & _ & _ & _ & _).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_B_D Col_A_B_F Col_A_B_B neq_F_B) as nCol_F_B_D.

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_C_q_R Col_A_B_q nCol_A_B_C) as OppositeSide_C_AB_R.
	pose proof (lemma_oppositeside_onray_PABC_RQP_QABC _ _ _ _ _ _ OppositeSide_C_AB_R OnRay_AD_C Col_A_B_A) as OppositeSide_D_AB_R.

	pose proof (proposition_31short _ _ _ _ BetS_F_A_B nCol_F_B_D) as (
		G & e & M & BetS_G_D_e & CongA_GDA_DAB & Par_Ge_FB & BetS_G_M_B & BetS_D_M_A
	).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_G_D_e) as Col_G_D_e.
	pose proof (by_prop_Col_order _ _ _ Col_G_D_e) as (_ & _ & _ & Col_G_e_D & _).
	pose proof (by_prop_Col_order _ _ _ Col_G_e_D) as (Col_e_G_D & _ & _ & _ & _).

	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_DAB CongA_GDA_DAB) as RightTriangle_GDA.

	pose proof (by_prop_Par_NC _ _ _ _ Par_Ge_FB) as (nCol_G_e_F & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_G_e_F) as (neq_G_e & _ & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_G_e) as neq_e_G.

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_Ge_FB Col_F_B_A neq_A_B) as Par_Ge_AB.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_Ge_AB) as Par_AB_Ge.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_M_B) as BetS_B_M_G.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_D_M_A) as Col_D_M_A.
	pose proof (by_prop_Col_order _ _ _ Col_D_M_A) as (_ & _ & _ & Col_D_A_M & _).
	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_B_M_G Col_D_A_M nCol_D_A_B) as OppositeSide_B_DA_G.

	pose proof (lemma_triangletoparallelogram _ _ _ _ _ Par_AB_Ge Col_G_e_D) as (E & Parallelogram_D_E_B_A & Col_G_e_E).

	pose proof (by_prop_Parallelogram_symmetric _ _ _ _ Parallelogram_D_E_B_A) as Parallelogram_B_A_D_E.
	pose proof (by_prop_Parallelogram_flip _ _ _ _ Parallelogram_B_A_D_E) as Parallelogram_A_B_E_D.

	pose proof (by_prop_Col_order _ _ _ Col_G_e_E) as (Col_e_G_E & _ & _ & _ & _).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_e_G_D Col_e_G_E neq_e_G) as Col_G_D_E.

	assert (Parallelogram_D_E_B_A_2 := Parallelogram_D_E_B_A).
	destruct Parallelogram_D_E_B_A_2 as (Par_DE_BA & Par_DA_EB).

	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_DA_EB) as TarskiPar_DA_EB.

	assert (TarskiPar_DA_EB_2 := TarskiPar_DA_EB).
	destruct TarskiPar_DA_EB_2 as (_ & neq_E_B & n_Meet_D_A_E_B & SameSide_E_B_DA).

	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_E_B_DA OppositeSide_B_DA_G) as OppositeSide_E_DA_G.

	assert (OppositeSide_E_DA_G_2 := OppositeSide_E_DA_G).
	destruct OppositeSide_E_DA_G_2 as (_ & _ & _ & nCol_D_A_E).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_D_A_E) as (_ & _ & neq_D_E & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_D_E) as neq_E_D.

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_GDA Col_G_D_E neq_E_D) as RightTriangle_EDA.

	pose proof (proposition_34 _ _ _ _ Parallelogram_D_E_B_A) as (
		Cong_DA_EB & Cong_DE_AB & CongA_EDA_ABE & CongA_DAB_BED & CongTriangles_EDA_ABE
	).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_DA_EB) as (_ & Cong_AD_EB & _).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_DE_AB) as Cong_AB_DE.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_DE) as (_ & _ & Cong_AB_ED).
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AB_AD Cong_AD_EB) as Cong_AB_EB.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_EB) as (_ & _ & Cong_AB_BE).

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_EDA_ABE) as CongA_ABE_EDA.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_DAB_BED) as CongA_BED_DAB.

	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_DAB CongA_BED_DAB) as RightTriangle_BED.
	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_EDA CongA_ABE_EDA) as RightTriangle_ABE.

	pose proof (
		by_def_Square
		_ _ _ _
		Cong_AB_ED Cong_AB_BE Cong_AB_DA
		RightTriangle_DAB RightTriangle_ABE RightTriangle_BED RightTriangle_EDA
	) as Square_A_B_E_D.

	exists E, D.
	split.
	exact Square_A_B_E_D .
	split.
	exact OppositeSide_D_AB_R.
	exact Parallelogram_A_B_E_D.
Qed.

End Euclid.
