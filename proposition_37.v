Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_rotate.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_diagonalsmeet.
Require Import ProofCheckingEuclid.lemma_triangletoparallelogram.
Require Import ProofCheckingEuclid.proposition_34.
Require Import ProofCheckingEuclid.proposition_35.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_37 :
	forall A B C D,
	Par A D B C ->
	EqAreaTri A B C D B C.
Proof.
	intros A B C D.
	intros Par_A_D_B_C.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq D D) as eq_D_D by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C A D A eq_A_A) as Col_A_D_A.
	pose proof (by_def_Col_from_eq_B_C A D D eq_D_D) as Col_A_D_D.
	
	pose proof (by_prop_Par_flip _ _ _ _ Par_A_D_B_C) as (Par_D_A_B_C & Par_A_D_C_B & Par_D_A_C_B).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_A_D_B_C) as Par_B_C_A_D.
	pose proof (by_prop_Par_flip _ _ _ _ Par_B_C_A_D) as (Par_C_B_A_D & Par_B_C_D_A & Par_C_B_D_A).
	pose proof (by_prop_Par_NC _ _ _ _ Par_A_D_B_C) as (nCol_A_D_B & nCol_A_B_C & nCol_D_B_C & nCol_A_D_C).
	
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_D_B) as (neq_A_D & neq_D_B & neq_A_B & neq_D_A & neq_B_D & neq_B_A).

	pose proof (lemma_triangletoparallelogram _ _ _ _ _ Par_C_B_A_D Col_A_D_A) as (E & Parallelogram_A_E_B_C & Col_A_D_E).
	pose proof (lemma_triangletoparallelogram _ _ _ _ _ Par_C_B_A_D Col_A_D_D) as (F & Parallelogram_D_F_B_C & Col_A_D_F).
	
	pose proof (by_prop_Col_order _ _ _ Col_A_D_E) as (Col_D_A_E & Col_D_E_A & Col_E_A_D & Col_A_E_D & Col_E_D_A).
	pose proof (by_prop_Col_order _ _ _ Col_A_D_F) as (Col_D_A_F & Col_D_F_A & Col_F_A_D & Col_A_F_D & Col_F_D_A).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_A_F Col_D_A_E neq_D_A) as Col_A_F_E.
	pose proof (by_prop_Col_order _ _ _ Col_A_F_E) as (_ & _ & Col_E_A_F & _ & _).

	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_A_E_B_C) as Parallelogram_E_B_C_A.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_D_F_B_C) as Parallelogram_F_B_C_D.

	assert (Parallelogram_E_B_C_A_2 := Parallelogram_E_B_C_A).
	destruct Parallelogram_E_B_C_A_2 as (Par_E_B_C_A & Par_E_A_B_C).

	pose proof (by_prop_Par_NC _ _ _ _ Par_E_B_C_A) as (_ & _ & _ & nCol_E_B_A).
	pose proof (by_prop_nCol_order _ _ _ nCol_E_B_A) as (_ & nCol_B_A_E & _ & _ & _).

	assert (Parallelogram_D_F_B_C_2 := Parallelogram_D_F_B_C).
	destruct Parallelogram_D_F_B_C_2 as (Par_D_F_B_C & Par_D_C_F_B).

	pose proof (by_prop_Par_NC _ _ _ _ Par_D_F_B_C) as (nCol_D_F_B & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_D_F_B) as (_ & _ & nCol_B_D_F & _ & _).

	pose proof (proposition_34 _ _ _ _ Parallelogram_E_B_C_A) as (_ & _ & _ & _ & CongTriangles_B_E_A_A_C_B).
	pose proof (proposition_34 _ _ _ _ Parallelogram_F_B_C_D) as (_ & _ & _ & _ & CongTriangles_B_F_D_D_C_B).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_B_E_A_A_C_B) as EqAreaTri_B_E_A_A_C_B.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_B_F_D_D_C_B) as EqAreaTri_B_F_D_D_C_B.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_B_E_A_A_C_B) as (EqAreaTri_B_E_A_C_B_A & _ & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_B_E_A_C_B_A) as EqAreaTri_C_B_A_B_E_A.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_C_B_A_B_E_A) as (_ & EqAreaTri_C_B_A_B_A_E & _ & _ & _).
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_B_F_D_D_C_B) as (EqAreaTri_B_F_D_C_B_D & _ & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_B_F_D_C_B_D) as EqAreaTri_C_B_D_B_F_D.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_C_B_D_B_F_D) as (_ & EqAreaTri_C_B_D_B_D_F & _ & _ & _).

	pose proof (proposition_35 _ _ _ _ _ _ Parallelogram_E_B_C_A Parallelogram_F_B_C_D Col_E_A_F Col_E_A_D) as EqAreaQuad_E_B_C_A_F_B_C_D.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_E_B_C_A_F_B_C_D) as (_ & _ & _ & _ & _ & EqAreaQuad_E_B_C_A_C_B_F_D & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_E_B_C_A_C_B_F_D) as EqAreaQuad_C_B_F_D_E_B_C_A.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_C_B_F_D_E_B_C_A) as (_ & _ & _ & _ & _ & EqAreaQuad_C_B_F_D_C_B_E_A & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_C_B_F_D_C_B_E_A) as EqAreaQuad_C_B_E_A_C_B_F_D.

	pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_E_B_C_A) as (M & BetS_E_M_C & BetS_B_M_A).
	pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_F_B_C_D) as (m & BetS_F_m_C & BetS_B_m_D).

	pose proof (by_def_Col_from_BetS_A_B_C B M A BetS_B_M_A) as Col_B_M_A.
	pose proof (by_def_Col_from_BetS_A_B_C B m D BetS_B_m_D) as Col_B_m_D.
	pose proof (by_prop_Col_order _ _ _ Col_B_M_A) as (_ & _ & _ & Col_B_A_M & _).
	pose proof (by_prop_Col_order _ _ _ Col_B_m_D) as (_ & _ & _ & Col_B_D_m & _).
	
	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_E_M_C Col_B_A_M nCol_B_A_E) as OppositeSide_E_B_A_C.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_E_B_A_C) as OppositeSide_C_B_A_E.
	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_F_m_C Col_B_D_m nCol_B_D_F) as OppositeSide_F_B_D_C.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_F_B_D_C) as OppositeSide_C_B_D_F.
	
	epose proof (axiom_halvesofequals C B A E C B D F EqAreaTri_C_B_A_B_A_E OppositeSide_C_B_A_E EqAreaTri_C_B_D_B_D_F OppositeSide_C_B_D_F EqAreaQuad_C_B_E_A_C_B_F_D) as EqAreaTri_C_B_A_C_B_D.

	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_C_B_A_C_B_D) as (_ & _ & _ & EqAreaTri_C_B_A_D_B_C & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_C_B_A_D_B_C) as EqAreaTri_D_B_C_C_B_A.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_D_B_C_C_B_A) as (_ & _ & _ & EqAreaTri_D_B_C_A_B_C & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_D_B_C_A_B_C) as EqAreaTri_A_B_C_D_B_C.

	exact EqAreaTri_A_B_C_D_B_C.
Qed.

End Euclid.
