Require Import ProofCheckingEuclid.by_def_CongTriangles.
Require Import ProofCheckingEuclid.by_def_Cross.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_def_Rectangle.
Require Import ProofCheckingEuclid.by_def_Square.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
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
	intros Cong_A_B_a_b.
	intros Square_A_B_C_D.
	intros Square_a_b_c_d.
	
	assert (Square_A_B_C_D_2 := Square_A_B_C_D).
	destruct Square_A_B_C_D_2 as (Cong_A_B_C_D & Cong_A_B_B_C & Cong_A_B_D_A & RightTriangle_D_A_B & RightTriangle_A_B_C & RightTriangle_B_C_D & RightTriangle_C_D_A).

	assert (Square_a_b_c_d_2 := Square_a_b_c_d).
	destruct Square_a_b_c_d_2 as (Cong_a_b_c_d & Cong_a_b_b_c & Cong_a_b_d_a & RightTriangle_d_a_b & RightTriangle_a_b_c & RightTriangle_b_c_d & RightTriangle_c_d_a).

	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_D_A_B RightTriangle_d_a_b) as CongA_D_A_B_d_a_b.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_A_B_D_A) as Cong_D_A_A_B.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_D_A_A_B Cong_A_B_a_b) as Cong_D_A_a_b.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_D_A_a_b Cong_a_b_d_a) as Cong_D_A_d_a.
	pose proof (lemma_squareparallelogram _ _ _ _ Square_A_B_C_D) as Parallelogram_A_B_C_D.
	pose proof (lemma_squareparallelogram _ _ _ _ Square_a_b_c_d) as Parallelogram_a_b_c_d.
	assert (Parallelogram_A_B_C_D_2 := Parallelogram_A_B_C_D).
	destruct Parallelogram_A_B_C_D_2 as (Par_A_B_C_D & Par_A_D_B_C).
	assert (Parallelogram_a_b_c_d_2 := Parallelogram_a_b_c_d).
	destruct Parallelogram_a_b_c_d_2 as (Par_a_b_c_d & Par_a_d_b_c).
	pose proof (by_prop_Par_NC _ _ _ _ Par_A_B_C_D) as (_ & _ & _ & nCol_A_B_D).
	pose proof (by_prop_Par_NC _ _ _ _ Par_a_b_c_d) as (_ & _ & _ & nCol_a_b_d).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_D_A_d_a) as (Cong_A_D_a_d & _ & _).
	pose proof (proposition_04 _ _ _ _ _ _ Cong_A_D_a_d Cong_A_B_a_b CongA_D_A_B_d_a_b) as (Cong_D_B_d_b & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_D_B_d_b) as (Cong_B_D_b_d & _ & _).
	pose proof (by_def_Triangle _ _ _ nCol_A_B_D) as Triangle_A_B_D.
	pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_A_B_a_b Cong_B_D_b_d Cong_A_D_a_d) as CongTriangles_A_B_D_a_b_d.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_A_B_D_a_b_d) as EqAreaTri_A_B_D_a_b_d.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_A_B_D_a_b_d) as (EqAreaTri_A_B_D_b_d_a & _ & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_A_B_D_b_d_a) as EqAreaTri_b_d_a_A_B_D.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_b_d_a_A_B_D) as (EqAreaTri_b_d_a_B_D_A & _ & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_b_d_a_B_D_A) as EqAreaTri_B_D_A_b_d_a.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_A_B_B_C) as Cong_B_C_A_B.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_B_C_A_B Cong_A_B_a_b) as Cong_B_C_a_b.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_B_C_a_b Cong_a_b_b_c) as Cong_B_C_b_c.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_A_B_C_D) as Cong_C_D_A_B.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_C_D_A_B Cong_A_B_a_b) as Cong_C_D_a_b.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_C_D_a_b Cong_a_b_c_d) as Cong_C_D_c_d.
	pose proof (by_prop_Par_NC _ _ _ _ Par_A_B_C_D) as (_ & _ & nCol_B_C_D & _).
	pose proof (by_def_Triangle _ _ _ nCol_B_C_D) as Triangle_B_C_D.
	pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_B_C_b_c Cong_C_D_c_d Cong_B_D_b_d) as CongTriangles_B_C_D_b_c_d.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_B_C_D_b_c_d) as EqAreaTri_B_C_D_b_c_d.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_B_C_D_b_c_d) as (_ & EqAreaTri_B_C_D_b_d_c & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_B_C_D_b_d_c) as EqAreaTri_b_d_c_B_C_D.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_b_d_c_B_C_D) as (_ & EqAreaTri_b_d_c_B_D_C & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_b_d_c_B_D_C) as EqAreaTri_B_D_C_b_d_c.
	pose proof (lemma_squarerectangle _ _ _ _ Square_A_B_C_D) as Rectangle_A_B_C_D.
	destruct Rectangle_A_B_C_D as (_ & _ & _ & _ & Cross_A_C_B_D).

	destruct Cross_A_C_B_D as (M & BetS_A_M_C & BetS_B_M_D).
	pose proof (lemma_squarerectangle _ _ _ _ Square_a_b_c_d) as Rectangle_a_b_c_d.
	destruct Rectangle_a_b_c_d as (_ & _ & _ & _ & Cross_a_c_b_d).

	destruct Cross_a_c_b_d as (m & BetS_a_m_c & BetS_b_m_d).
	
	assert (BetS B M D \/ eq B M \/ eq M D) as BetS_B_M_D' by (left; exact BetS_B_M_D).
	assert (BetS b m d \/ eq b m \/ eq m d) as BetS_b_m_d' by (left; exact BetS_b_m_d).

	epose proof (
		axiom_paste3
		B D A C M
		b d a c m
		EqAreaTri_B_D_A_b_d_a
		EqAreaTri_B_D_C_b_d_c
		BetS_A_M_C
		BetS_B_M_D'
		BetS_a_m_c
		BetS_b_m_d'
	) as EqAreaQuad_B_A_D_C_b_a_d_c.

	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_B_A_D_C_b_a_d_c) as (_ & _ & _ & EqAreaQuad_B_A_D_C_a_b_c_d & _ & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_B_A_D_C_a_b_c_d) as EqAreaQuad_a_b_c_d_B_A_D_C.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_a_b_c_d_B_A_D_C) as (_ & _ & _ & EqAreaQuad_a_b_c_d_A_B_C_D & _ & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_a_b_c_d_A_B_C_D) as EqAreaQuad_A_B_C_D_a_b_c_d.

	exact EqAreaQuad_A_B_C_D_a_b_c_d.
Qed.

End Euclid.
