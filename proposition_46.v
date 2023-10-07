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

	pose proof (lemma_extension B A A B neq_B_A neq_A_B) as (F & BetS_B_A_F & _).

	pose proof (by_def_Col_from_eq_A_C B F B eq_B_B) as Col_B_F_B.
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_F) as BetS_F_A_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_A_F) as (neq_A_F & _ & neq_B_F).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_F_A_B) as (_ & neq_F_A & neq_F_B).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_A_F) as Col_B_A_F.
	pose proof (by_prop_Col_order _ _ _ Col_B_A_F) as (Col_A_B_F & Col_A_F_B & Col_F_B_A & Col_B_F_A & Col_F_A_B).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_A_R Col_B_A_B Col_B_A_F neq_B_F) as nCol_B_F_R.

	pose proof (proposition_11B _ _ _ _ BetS_B_A_F nCol_B_F_R) as (C & RightTriangle_B_A_C & OppositeSide_C_B_F_R).

	pose proof (by_def_Col_from_eq_B_C C A A eq_A_A) as Col_C_A_A.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_B_A_C) as RightTriangle_C_A_B.

	destruct OppositeSide_C_B_F_R as (q & BetS_C_q_R & Col_B_F_q & nCol_B_F_C).

	pose proof (by_prop_Col_order _ _ _ Col_B_F_q) as (Col_F_B_q & _ & _ & _ & _).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_F_B_A Col_F_B_q neq_F_B) as Col_B_A_q.
	pose proof (by_prop_Col_order _ _ _ Col_B_A_q) as (Col_A_B_q & _ & _ & _ & _).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_F_C Col_B_F_A Col_B_F_B neq_A_B) as nCol_A_B_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (_ & neq_B_C & neq_A_C & _ & neq_C_B & neq_C_A).

	pose proof (lemma_layoff _ _ _ _ neq_A_C neq_A_B) as (D & OnRay_A_C_D & Cong_A_D_A_B).

	assert (eq D D) as eq_D_D by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C D A D eq_D_D) as Col_D_A_D.

	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_A_C_D) as OnRay_A_D_C.
	pose proof (by_prop_OnRay_neq_A_B _ _ _ OnRay_A_D_C) as neq_A_D.
	pose proof (by_prop_neq_symmetric _ _ neq_A_D) as neq_D_A.

	pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_A_C_D) as Col_A_C_D.
	pose proof (by_prop_Col_order _ _ _ Col_A_C_D) as (Col_C_A_D & _ & _ & _ & _).
	
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_A_D_A_B) as (Cong_D_A_B_A & Cong_D_A_A_B & Cong_A_D_B_A).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_A_D_A_B) as Cong_A_B_A_D.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_A_B_A_D) as (Cong_B_A_D_A & Cong_B_A_A_D & Cong_A_B_D_A).

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_C_A_B Col_C_A_D neq_D_A) as RightTriangle_D_A_B.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_C_A_B Col_C_A_A Col_C_A_D neq_A_D) as nCol_A_D_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_D_B) as (_ & _ & _ & nCol_A_B_D & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_D_B) as (nCol_D_A_B & _ & _ & _ & _).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_B_D Col_A_B_F Col_A_B_B neq_F_B) as nCol_F_B_D.

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_C_q_R Col_A_B_q nCol_A_B_C) as OppositeSide_C_A_B_R.
	pose proof (lemma_oppositeside_onray_PABC_RQP_QABC _ _ _ _ _ _ OppositeSide_C_A_B_R OnRay_A_D_C Col_A_B_A) as OppositeSide_D_A_B_R.

	pose proof (proposition_31short _ _ _ _ BetS_F_A_B nCol_F_B_D) as (
		G & e & M & BetS_G_D_e & CongA_G_D_A_D_A_B & Par_G_e_F_B & BetS_G_M_B & BetS_D_M_A
	).

	pose proof (by_def_Col_from_BetS_A_B_C G D e BetS_G_D_e) as Col_G_D_e.
	pose proof (by_prop_Col_order _ _ _ Col_G_D_e) as (_ & _ & _ & Col_G_e_D & _).
	pose proof (by_prop_Col_order _ _ _ Col_G_e_D) as (Col_e_G_D & _ & _ & _ & _).

	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_D_A_B CongA_G_D_A_D_A_B) as RightTriangle_G_D_A.

	pose proof (by_prop_Par_NC _ _ _ _ Par_G_e_F_B) as (nCol_G_e_F & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_G_e_F) as (neq_G_e & _ & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_G_e) as neq_e_G.

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_G_e_F_B Col_F_B_A neq_A_B) as Par_G_e_A_B.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_G_e_A_B) as Par_A_B_G_e.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_M_B) as BetS_B_M_G.
	pose proof (by_def_Col_from_BetS_A_B_C D M A BetS_D_M_A) as Col_D_M_A.
	pose proof (by_prop_Col_order _ _ _ Col_D_M_A) as (_ & _ & _ & Col_D_A_M & _).
	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_B_M_G Col_D_A_M nCol_D_A_B) as OppositeSide_B_D_A_G.

	pose proof (lemma_triangletoparallelogram _ _ _ _ _ Par_A_B_G_e Col_G_e_D) as (E & Parallelogram_D_E_B_A & Col_G_e_E).

	pose proof (by_prop_Parallelogram_symmetric _ _ _ _ Parallelogram_D_E_B_A) as Parallelogram_B_A_D_E.
	pose proof (by_prop_Parallelogram_flip _ _ _ _ Parallelogram_B_A_D_E) as Parallelogram_A_B_E_D.

	pose proof (by_prop_Col_order _ _ _ Col_G_e_E) as (Col_e_G_E & _ & _ & _ & _).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_e_G_D Col_e_G_E neq_e_G) as Col_G_D_E.

	assert (Parallelogram_D_E_B_A_2 := Parallelogram_D_E_B_A).
	destruct Parallelogram_D_E_B_A_2 as (Par_D_E_B_A & Par_D_A_E_B).

	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_D_A_E_B) as TarskiPar_D_A_E_B.

	assert (TarskiPar_D_A_E_B_2 := TarskiPar_D_A_E_B).
	destruct TarskiPar_D_A_E_B_2 as (_ & neq_E_B & n_Meet_D_A_E_B & SameSide_E_B_D_A).

	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_E_B_D_A OppositeSide_B_D_A_G) as OppositeSide_E_D_A_G.

	assert (OppositeSide_E_D_A_G_2 := OppositeSide_E_D_A_G).
	destruct OppositeSide_E_D_A_G_2 as (_ & _ & _ & nCol_D_A_E).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_D_A_E) as (_ & _ & neq_D_E & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_D_E) as neq_E_D.

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_G_D_A Col_G_D_E neq_E_D) as RightTriangle_E_D_A.

	pose proof (proposition_34 _ _ _ _ Parallelogram_D_E_B_A) as (
		Cong_D_A_E_B & Cong_D_E_A_B & CongA_E_D_A_A_B_E & CongA_D_A_B_B_E_D & CongTriangles_E_D_A_A_B_E
	).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_D_A_E_B) as (_ & Cong_A_D_E_B & _).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_D_E_A_B) as Cong_A_B_D_E.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_A_B_D_E) as (_ & _ & Cong_A_B_E_D).
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_A_B_A_D Cong_A_D_E_B) as Cong_A_B_E_B.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_A_B_E_B) as (_ & _ & Cong_A_B_B_E).

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_E_D_A_A_B_E) as CongA_A_B_E_E_D_A.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_D_A_B_B_E_D) as CongA_B_E_D_D_A_B.

	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_D_A_B CongA_B_E_D_D_A_B) as RightTriangle_B_E_D.
	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_E_D_A CongA_A_B_E_E_D_A) as RightTriangle_A_B_E.

	pose proof (
		by_def_Square
		_ _ _ _
		Cong_A_B_E_D Cong_A_B_B_E Cong_A_B_D_A
		RightTriangle_D_A_B RightTriangle_A_B_E RightTriangle_B_E_D RightTriangle_E_D_A
	) as Square_A_B_E_D.

	exists E, D.
	split.
	exact Square_A_B_E_D .
	split.
	exact OppositeSide_D_A_B_R.
	exact Parallelogram_A_B_E_D.
Qed.

End Euclid.
