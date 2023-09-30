Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_CongTriangles.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_SameSide_flip.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_interior5.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_sameside_onray_EFAC_BFG_EGAC.
Require Import ProofCheckingEuclid.lemma_samesidecollinear.
Require Import ProofCheckingEuclid.lemma_samesidetransitive.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_23C.
Require Import ProofCheckingEuclid.proposition_42.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_42B :
	forall B C D E J K R a b c e,
	Triangle a b c ->
	Midpoint b e c ->
	nCol J D K ->
	Midpoint B E C ->
	Cong E C e c ->
	nCol R E C ->
	exists X Z, Parallelogram X E C Z /\ EqAreaQuad a b e c X E C Z /\ CongA C E X J D K /\ SameSide R X E C.
Proof.
	intros B C D E J K R a b c e.
	intros Triangle_a_b_c.
	intros Midpoint_b_e_c.
	intros nCol_J_D_K.
	intros Midpoint_B_E_C.
	intros Cong_E_C_e_c.
	intros nCol_R_E_C.

	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq b b) as eq_b_b by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C b c b eq_b_b) as Col_b_c_b.
	pose proof (by_def_Col_from_eq_A_C B C B eq_B_B) as Col_B_C_B.
	pose proof (by_def_Col_from_eq_A_B B B C eq_B_B) as Col_B_B_C.
	pose proof (by_def_Col_from_eq_B_C E C C eq_C_C) as Col_E_C_C.
	pose proof (by_def_Col_from_eq_A_C C B C eq_C_C) as Col_C_B_C.

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_a_b_c) as nCol_a_b_c.
	pose proof (by_prop_nCol_order _ _ _ nCol_a_b_c) as (nCol_b_a_c & nCol_b_c_a & nCol_c_a_b & nCol_a_c_b & nCol_c_b_a).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_a_b_c) as (neq_a_b & neq_b_c & neq_a_c & neq_b_a & neq_c_b & neq_c_a).

	destruct Midpoint_b_e_c as (BetS_b_e_c & Cong_b_e_e_c).
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_b_e_c) as BetS_c_e_b.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_b_e_c) as (neq_e_c & neq_b_e & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_c_e_b) as (neq_e_b & neq_c_e & _).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_b_e_c) as Col_b_e_c.
	pose proof (by_prop_Col_order _ _ _ Col_b_e_c) as (Col_e_b_c & Col_e_c_b & Col_c_b_e & Col_b_c_e & Col_c_e_b).
	
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_b_e_e_c) as (Cong_e_b_c_e & Cong_e_b_e_c & Cong_b_e_c_e).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_b_e_e_c) as Cong_e_c_b_e.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_e_c_b_e) as (Cong_c_e_e_b & Cong_c_e_b_e & Cong_e_c_e_b).

	assert (Midpoint_B_E_C_2 := Midpoint_B_E_C).
	destruct Midpoint_B_E_C_2 as (BetS_B_E_C & Cong_B_E_E_C).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_E_C) as BetS_C_E_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_E_C) as (neq_E_C & neq_B_E & neq_B_C).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_E_B) as (neq_E_B & neq_C_E & neq_C_B).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_E_C) as Col_B_E_C.
	pose proof (by_prop_Col_order _ _ _ Col_B_E_C) as (Col_E_B_C & Col_E_C_B & Col_C_B_E & Col_B_C_E & Col_C_E_B).
	
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_B_E_E_C) as (Cong_E_B_C_E & Cong_E_B_E_C & Cong_B_E_C_E).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_B_E_E_C) as Cong_E_C_B_E.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_E_C_B_E) as (Cong_C_E_E_B & Cong_C_E_B_E & Cong_E_C_E_B).
	
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_E_C_e_c) as (Cong_C_E_c_e & Cong_C_E_e_c & Cong_E_C_c_e).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_E_C_e_c) as Cong_e_c_E_C.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_e_c_E_C) as (Cong_c_e_C_E & Cong_c_e_E_C & Cong_e_c_C_E).
	
	pose proof (by_prop_nCol_order _ _ _ nCol_R_E_C) as (nCol_E_R_C & nCol_E_C_R & nCol_C_R_E & nCol_R_C_E & nCol_C_E_R).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_E_C_R Col_E_C_B Col_E_C_C neq_B_C) as nCol_B_C_R.
	pose proof (proposition_23C _ _ _ _ _ _ neq_B_C nCol_a_b_c nCol_B_C_R) as (P & H & OnRay_B_C_H & CongA_P_B_H_a_b_c & SameSide_P_R_B_C).

	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_B_C_H) as OnRay_B_H_C.

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_P_B_H_a_b_c) as CongA_a_b_c_P_B_H.

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_P_R_B_C) as (SameSide_R_P_B_C & _ & _).

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_B_E_E_C Cong_E_C_e_c) as Cong_B_E_e_c.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_B_E_e_c) as (Cong_E_B_c_e & Cong_E_B_e_c & Cong_B_E_c_e).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_B_E_e_c) as Cong_e_c_B_E.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_e_c_B_E) as (Cong_c_e_E_B & Cong_c_e_B_E & Cong_e_c_E_B).

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_B_E_e_c Cong_e_c_b_e) as Cong_B_E_b_e.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_B_E_b_e) as (Cong_E_B_e_b & Cong_E_B_b_e & Cong_B_E_e_b).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_B_E_b_e) as Cong_b_e_B_E.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_b_e_B_E) as (Cong_e_b_E_B & Cong_e_b_B_E & Cong_b_e_E_B).

	pose proof (cn_sumofparts _ _ _ _ _ _ Cong_B_E_b_e Cong_E_C_e_c BetS_B_E_C BetS_b_e_c) as Cong_B_C_b_c.
	
	assert (SameSide_R_P_B_C_2 := SameSide_R_P_B_C).
	destruct SameSide_R_P_B_C_2 as (_ & _ & _ & _ & _ & _ & _ & _ & nCol_B_C_P).
	pose proof (by_prop_nCol_order _ _ _ nCol_B_C_P) as (nCol_C_B_P & nCol_C_P_B & nCol_P_B_C & nCol_B_P_C & nCol_P_C_B).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_C_P) as (_ & neq_C_P & neq_B_P & _ & neq_P_C & neq_P_B).

	pose proof (lemma_layoff _ _ _ _ neq_B_P neq_b_a) as (A & OnRay_B_P_A & Cong_B_A_b_a).
	
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_B_A_b_a) as (Cong_A_B_a_b & Cong_A_B_b_a & Cong_B_A_a_b).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_B_A_b_a) as Cong_b_a_B_A.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_b_a_B_A) as (Cong_a_b_A_B & Cong_a_b_B_A & Cong_b_a_A_B).

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_a_b_c_P_B_H OnRay_B_P_A OnRay_B_H_C) as CongA_a_b_c_A_B_C.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_a_b_c_A_B_C) as CongA_A_B_C_a_b_c.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_a_b_c_A_B_C) as nCol_A_B_C.
	pose proof (by_def_Triangle _ _ _ nCol_A_B_C) as Triangle_A_B_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & _ & neq_A_C & neq_B_A & _ & neq_C_A).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_C_A Col_B_C_B Col_B_C_E neq_B_E) as nCol_B_E_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_B_E_A) as (_ & _ & _ & _ & nCol_A_E_B).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_b_c_a Col_b_c_b Col_b_c_e neq_b_e) as nCol_b_e_a.
	pose proof (by_prop_nCol_order _ _ _ nCol_b_e_a) as (_ & _ & _ & _ & nCol_a_e_b).

	pose proof (proposition_04 _ _ _ _ _ _ Cong_B_A_b_a Cong_B_C_b_c CongA_A_B_C_a_b_c) as (Cong_A_C_a_c & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_A_C_a_c) as (Cong_C_A_c_a & Cong_C_A_a_c & Cong_A_C_c_a).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_A_C_a_c) as Cong_a_c_A_C.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_a_c_A_C) as (Cong_c_a_C_A & Cong_c_a_A_C & Cong_a_c_C_A).

	pose proof (lemma_interior5 _ _ _ _ _ _ _ _ BetS_B_E_C BetS_b_e_c Cong_B_E_b_e Cong_E_C_e_c Cong_B_A_b_a Cong_C_A_c_a) as Cong_E_A_e_a.
	
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_E_A_e_a) as (Cong_A_E_a_e & Cong_A_E_e_a & Cong_E_A_a_e).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_E_A_e_a) as Cong_e_a_E_A.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_e_a_E_A) as (Cong_a_e_A_E & Cong_a_e_E_A & Cong_e_a_A_E).

	pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_A_E_a_e Cong_E_B_e_b Cong_A_B_a_b) as CongTriangles_A_E_B_a_e_b.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_A_E_B_a_e_b) as EqAreaTri_A_E_B_a_e_b.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_C_B_A Col_C_B_C Col_C_B_E neq_C_E) as nCol_C_E_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_C_E_A) as (_ & _ & _ & _ & nCol_A_E_C).

	pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_A_E_a_e Cong_E_C_e_c Cong_A_C_a_c) as CongTriangles_A_E_C_a_e_c.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_A_E_C_a_e_c) as EqAreaTri_A_E_C_a_e_c.

	assert (eq E E) as eq_E_E by (reflexivity).
	assert (eq e e) as eq_e_e by (reflexivity).

	assert (BetS A E E \/ eq A E \/ eq E E) as eq_E_E' by (right; right; exact eq_E_E).
	assert (BetS a e e \/ eq a e \/ eq e e) as eq_e_e' by (right; right; exact eq_e_e).

	epose proof (
		axiom_paste3
		A E B C E a e b c e
		EqAreaTri_A_E_B_a_e_b
		EqAreaTri_A_E_C_a_e_c
		BetS_B_E_C
		eq_E_E'
		BetS_b_e_c
		eq_e_e'
	) as EqAreaQuad_A_B_E_C_a_b_e_c.
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_A_B_E_C_a_b_e_c) as EqAreaQuad_a_b_e_c_A_B_E_C.

	pose proof (proposition_42 _ _ _ _ _ _ _ Triangle_A_B_C nCol_J_D_K Midpoint_B_E_C) as (F & G & Parallelogram_F_E_C_G & EqAreaQuad_A_B_E_C_F_E_C_G & CongA_C_E_F_J_D_K & Col_F_G_A).

	assert (Parallelogram_F_E_C_G_2 := Parallelogram_F_E_C_G).
	destruct Parallelogram_F_E_C_G_2 as (Par_F_E_C_G & Par_F_G_E_C).

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_F_G_E_C) as Par_E_C_F_G.
	pose proof (by_prop_Par_flip _ _ _ _ Par_E_C_F_G) as (_ & Par_E_C_G_F & _).

	pose proof (by_prop_Col_order _ _ _ Col_F_G_A) as (Col_G_F_A & _ & _ & _ & _).

	pose proof (axiom_EqAreaQuad_transitive _ _ _ _ _ _ _ _ _ _ _ _ EqAreaQuad_a_b_e_c_A_B_E_C EqAreaQuad_A_B_E_C_F_E_C_G) as EqAreaQuad_a_b_e_c_F_E_C_G.

	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_R_P_B_C Col_B_B_C OnRay_B_P_A) as SameSide_R_A_B_C.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_R_A_B_C) as SameSide_R_A_C_B.
	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_R_A_C_B Col_C_B_E neq_C_E) as SameSide_R_A_C_E.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_R_A_C_E) as (SameSide_A_R_C_E & _ & _).
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_R_A_C_E) as SameSide_R_A_E_C.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_A_R_C_E) as SameSide_A_R_E_C.


	(* assert by cases *)
	assert (SameSide R F E C) as SameSide_R_F_E_C.
	assert (eq A F \/ neq A F) as [eq_A_F|neq_A_F] by (apply Classical_Prop.classic).
	{
		(* case eq_A_F *)
		assert (SameSide R F E C) as SameSide_R_F_E_C by (rewrite <- eq_A_F; exact SameSide_R_A_E_C).

		exact SameSide_R_F_E_C.
	}
	{
		(* case neq_A_F *)
		pose proof (by_prop_Par_collinear _ _ _ _ _ Par_E_C_G_F Col_G_F_A neq_A_F) as Par_E_C_A_F.
		pose proof (by_prop_Par_flip _ _ _ _ Par_E_C_A_F) as (_ & Par_E_C_F_A & _).
		pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_E_C_F_A) as TarskiPar_E_C_F_A.
		assert (TarskiPar_E_C_F_A_2 := TarskiPar_E_C_F_A).
		destruct TarskiPar_E_C_F_A_2 as (_ & neq_F_A & n_Meet_E_C_F_A & SameSide_F_A_E_C).

		pose proof (lemma_samesidetransitive _ _ _ _ _ SameSide_F_A_E_C SameSide_A_R_E_C) as SameSide_F_R_E_C.
		pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_F_R_E_C) as (SameSide_R_F_E_C & _ & _).

		exact SameSide_R_F_E_C.
	}

	exists F, G.
	split.
	exact Parallelogram_F_E_C_G.
	split.
	exact EqAreaQuad_a_b_e_c_F_E_C_G.
	split.
	exact CongA_C_E_F_J_D_K.
	exact SameSide_R_F_E_C.
Qed.

End Euclid.
