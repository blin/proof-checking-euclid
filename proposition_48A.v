Require Import ProofCheckingEuclid.by_def_CongTriangles.
Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B .
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_def_Rectangle.
Require Import ProofCheckingEuclid.by_def_Square.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_Lt_trichotomous.
Require Import ProofCheckingEuclid.by_prop_OnRay_assert.
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
	intros EqAreaQuad_A_B_C_D_a_b_c_d.
	

	assert (Square_A_B_C_D_2 := Square_A_B_C_D).
	destruct Square_A_B_C_D_2 as (_ & _ & Cong_A_B_D_A & RightTriangle_D_A_B & _ & _ & _).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_A_B_D_A) as (_ & _ & Cong_A_B_A_D).

	pose proof (lemma_squarerectangle _ _ _ _ Square_A_B_C_D) as Rectangle_A_B_C_D.
	assert (Rectangle_A_B_C_D_2 := Rectangle_A_B_C_D).
	destruct Rectangle_A_B_C_D as (_ & _ & _ & _ & Cross_A_C_B_D).

	pose proof (lemma_squareparallelogram _ _ _ _ Square_A_B_C_D) as Parallelogram_A_B_C_D.
	assert (Parallelogram_A_B_C_D_2 := Parallelogram_A_B_C_D).
	destruct Parallelogram_A_B_C_D_2 as (Par_A_B_C_D & Par_A_D_B_C).

	pose proof (by_prop_Par_NC _ _ _ _ Par_A_B_C_D) as (_ & _ & _ & nCol_A_B_D).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_D) as (_ & _ & nCol_D_A_B & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_D) as (neq_A_B & _ & _ & _ & _ & _).
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_D_A_B) as CongA_D_A_B_D_A_B.

	pose proof (by_def_Triangle _ _ _ nCol_D_A_B) as Triangle_D_A_B.

	pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_A_C_B_D nCol_A_B_D) as (OppositeSide_A_B_D_C & _ & _ & _).
	
	assert (Square_a_b_c_d_2 := Square_a_b_c_d).
	destruct Square_a_b_c_d_2 as (_ & _ & Cong_a_b_d_a & RightTriangle_d_a_b & _ & _ & _).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_a_b_d_a) as (_ & _ & Cong_a_b_a_d).

	pose proof (lemma_squarerectangle _ _ _ _ Square_a_b_c_d) as Rectangle_a_b_c_d.
	assert (Rectangle_a_b_c_d_2 := Rectangle_a_b_c_d).
	destruct Rectangle_a_b_c_d as (_ & _ & _ & _ & Cross_a_c_b_d).

	pose proof (lemma_squareparallelogram _ _ _ _ Square_a_b_c_d) as Parallelogram_a_b_c_d.
	assert (Parallelogram_a_b_c_d_2 := Parallelogram_a_b_c_d).
	destruct Parallelogram_a_b_c_d_2 as (Par_a_b_c_d & Par_a_d_b_c).

	pose proof (by_prop_Par_NC _ _ _ _ Par_a_b_c_d) as (_ & _ & _ & nCol_a_b_d).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_a_b_d) as (neq_a_b & _ & _ & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_a_b_d) as (_ & _ & nCol_d_a_b & _ & _).
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_d_a_b) as CongA_d_a_b_d_a_b.

	pose proof (by_def_Triangle _ _ _ nCol_d_a_b) as Triangle_d_a_b.

	pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_a_c_b_d nCol_a_b_d) as (OppositeSide_a_b_d_c & _ & _ & _).

	pose proof (proposition_34 _ _ _ _ Parallelogram_A_B_C_D) as (_ & _ & _ & _ & CongTriangles_B_A_D_D_C_B).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_B_A_D_D_C_B) as EqAreaTri_B_A_D_D_C_B.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_B_A_D_D_C_B) as (_ & _ & _ & _ & EqAreaTri_B_A_D_B_D_C).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_B_A_D_B_D_C) as EqAreaTri_B_D_C_B_A_D.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_B_D_C_B_A_D) as (_ & _ & EqAreaTri_B_D_C_A_B_D & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_B_D_C_A_B_D) as EqAreaTri_A_B_D_B_D_C.

	pose proof (proposition_34 _ _ _ _ Parallelogram_a_b_c_d) as (_ & _ & _ & _ & CongTriangles_b_a_d_d_c_b).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_b_a_d_d_c_b) as EqAreaTri_b_a_d_d_c_b.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_b_a_d_d_c_b) as (_ & _ & _ & _ & EqAreaTri_b_a_d_b_d_c).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_b_a_d_b_d_c) as EqAreaTri_b_d_c_b_a_d.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_b_d_c_b_a_d) as (_ & _ & EqAreaTri_b_d_c_a_b_d & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_b_d_c_a_b_d) as EqAreaTri_a_b_d_b_d_c.
	
	pose proof (
		axiom_halvesofequals
		_ _ _ _ _ _ _ _
		EqAreaTri_A_B_D_B_D_C OppositeSide_A_B_D_C EqAreaTri_a_b_d_b_d_c OppositeSide_a_b_d_c EqAreaQuad_A_B_C_D_a_b_c_d
	) as EqAreaTri_A_B_D_a_b_d.

	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_A_B_D_a_b_d) as EqAreaTri_a_b_d_A_B_D.


	assert (~ Lt a b A B) as n_Lt_a_b_A_B.
	{
		intro Lt_a_b_A_B.

		pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_a_b_A_B Cong_a_b_a_d) as Lt_a_d_A_B.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_a_d_A_B Cong_A_B_A_D) as Lt_a_d_A_D.

		assert (Lt_a_b_A_B_2 := Lt_a_b_A_B).
		destruct Lt_a_b_A_B_2 as (E & BetS_A_E_B & Cong_A_E_a_b).

		pose proof (by_def_OnRay_from_BetS_A_E_B A B E BetS_A_E_B neq_A_B) as OnRay_A_B_E.


		destruct Lt_a_d_A_D as (F & BetS_A_F_D & Cong_A_F_a_d).

		pose proof (by_prop_BetS_notequal _ _ _ BetS_A_F_D) as (_ & _ & neq_A_D).

		pose proof (by_prop_Cong_flip _ _ _ _ Cong_A_F_a_d) as (Cong_F_A_d_a & _ & _).
		
		pose proof (by_def_OnRay_from_BetS_A_E_B A D F BetS_A_F_D neq_A_D) as OnRay_A_D_F.

		pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_D_A_B_D_A_B OnRay_A_D_F OnRay_A_B_E) as CongA_D_A_B_F_A_E.
		pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_D_A_B_F_A_E) as CongA_F_A_E_D_A_B.

		pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_D_A_B CongA_F_A_E_D_A_B) as RightTriangle_F_A_E.
		pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_F_A_E RightTriangle_d_a_b) as CongA_F_A_E_d_a_b.
		pose proof (proposition_04 _ _ _ _ _ _ Cong_A_F_a_d Cong_A_E_a_b CongA_F_A_E_d_a_b) as (Cong_F_E_d_b & _ & _).
		pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_F_A_d_a Cong_A_E_a_b Cong_F_E_d_b) as CongTriangles_F_A_E_d_a_b.
		pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_F_A_E_d_a_b) as EqAreaTri_F_A_E_d_a_b.
		pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_F_A_E_d_a_b) as (EqAreaTri_F_A_E_a_b_d & _ & _ & _ & _).
		pose proof (axiom_EqAreaTri_transitive _ _ _ _ _ _ _ _ _ EqAreaTri_F_A_E_a_b_d EqAreaTri_a_b_d_A_B_D) as EqAreaTri_F_A_E_A_B_D.
		pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_F_A_E_A_B_D) as (_ & _ & _ & _ & EqAreaTri_F_A_E_D_A_B).
		pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_F_A_E_D_A_B) as EqAreaTri_D_A_B_F_A_E.

		pose proof (axiom_deZolt2 _ _ _ _ _ Triangle_D_A_B BetS_A_F_D BetS_A_E_B) as n_EqAreaTri_D_A_B_F_A_E.

		contradict EqAreaTri_D_A_B_F_A_E.
		exact n_EqAreaTri_D_A_B_F_A_E.
	}


	assert (~ Lt A B a b) as n_Lt_A_B_a_b.
	{
		intro Lt_A_B_a_b.

		pose proof (by_prop_Lt_congruence_smaller _ _ _ _ _ _ Lt_A_B_a_b Cong_A_B_A_D) as Lt_A_D_a_b.
		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_A_D_a_b Cong_a_b_a_d) as Lt_A_D_a_d.

		assert (Lt_A_B_a_b_2 := Lt_A_B_a_b).
		destruct Lt_A_B_a_b_2 as (e & BetS_a_e_b & Cong_a_e_A_B).

		pose proof (by_def_OnRay_from_BetS_A_E_B a b e BetS_a_e_b neq_a_b) as OnRay_a_b_e.

		destruct Lt_A_D_a_d as (f & BetS_a_f_d & Cong_a_f_A_D).

		pose proof (by_prop_BetS_notequal _ _ _ BetS_a_f_d) as (_ & _ & neq_a_d).
		
		pose proof (by_def_OnRay_from_BetS_A_E_B a d f BetS_a_f_d neq_a_d) as OnRay_a_d_f.

		pose proof (by_prop_Cong_flip _ _ _ _ Cong_a_f_A_D) as (Cong_f_a_D_A & _ & _).


		pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_d_a_b_d_a_b OnRay_a_d_f OnRay_a_b_e) as CongA_d_a_b_f_a_e.
		pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_d_a_b_f_a_e) as CongA_f_a_e_d_a_b.
		pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_d_a_b CongA_f_a_e_d_a_b) as RightTriangle_f_a_e.
		pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_f_a_e RightTriangle_D_A_B) as CongA_f_a_e_D_A_B.
		pose proof (proposition_04 _ _ _ _ _ _ Cong_a_f_A_D Cong_a_e_A_B CongA_f_a_e_D_A_B) as (Cong_f_e_D_B & _ & _).
		pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_f_a_D_A Cong_a_e_A_B Cong_f_e_D_B) as CongTriangles_f_a_e_D_A_B.
		pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_f_a_e_D_A_B) as EqAreaTri_f_a_e_D_A_B.
		pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_f_a_e_D_A_B) as (EqAreaTri_f_a_e_A_B_D & _ & _ & _ & _).
		pose proof (axiom_EqAreaTri_transitive _ _ _ _ _ _ _ _ _ EqAreaTri_f_a_e_A_B_D EqAreaTri_A_B_D_a_b_d) as EqAreaTri_f_a_e_a_b_d.
		pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_f_a_e_a_b_d) as (_ & _ & _ & _ & EqAreaTri_f_a_e_d_a_b).
		pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_f_a_e_d_a_b) as EqAreaTri_d_a_b_f_a_e.

		pose proof (axiom_deZolt2 _ _ _ _ _ Triangle_d_a_b BetS_a_f_d BetS_a_e_b) as n_EqAreaTri_d_a_b_f_a_e.

		contradict EqAreaTri_d_a_b_f_a_e.
		exact n_EqAreaTri_d_a_b_f_a_e.
	}

	pose proof (by_prop_Lt_trichotomous _ _ _ _ n_Lt_A_B_a_b n_Lt_a_b_A_B neq_A_B neq_a_b) as Cong_A_B_a_b.

	exact Cong_A_B_a_b.
Qed.

End Euclid.
