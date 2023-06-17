Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_extensionunique.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_interior5.
Require Import ProofCheckingEuclid.lemma_linereflectionisometry.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
Require Import ProofCheckingEuclid.lemma_rightreverse.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_right_triangle.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.proposition_10.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

(*
	There are three notable scenarios here.
	1. SS C H A B
	2. OS C A B H
	3. ~ SS C H A B /\ OS C A B H -> A B C H are not in the same plane.
*)
Lemma lemma_right_triangle_same_base_cong_side_cong_hypotenuse :
	forall A B C H,
	RightTriangle A B C ->
	RightTriangle A B H ->
	Cong B C B H ->
	Cong A C A H.
Proof.
	intros A B C H.
	intros RightTriangle_A_B_C.
	intros RightTriangle_A_B_H.
	intros Cong_B_C_B_H.

	pose proof (cn_congruencereflexive A C) as Cong_A_C_A_C.

	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_A_B_C) as RightTriangle_C_B_A.

	assert (RightTriangle_A_B_C2 := RightTriangle_A_B_C).
	destruct RightTriangle_A_B_C2 as (D & BetS_A_B_D & Cong_A_B_D_B & Cong_A_C_D_C & _).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_A_B_D_B) as Cong_D_B_A_B.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_A_C_D_C) as (Cong_C_A_C_D & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_A_B_D_B) as (Cong_B_A_B_D & _ & _).

	assert (RightTriangle_A_B_H2 := RightTriangle_A_B_H).
	destruct RightTriangle_A_B_H2 as (F & BetS_A_B_F & Cong_A_B_F_B & Cong_A_H_F_H & _).

	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_D_B_A_B Cong_A_B_F_B) as Cong_D_B_F_B.
	pose proof (lemma_doublereverse _ _ _ _ Cong_D_B_F_B) as (Cong_B_F_B_D & _).

	pose proof (lemma_doublereverse _ _ _ _ Cong_B_C_B_H) as (_ & Cong_C_B_H_B).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_B_C_B_H) as (_ & Cong_C_B_B_H & _).

	pose proof (lemma_extensionunique _ _ _ _ BetS_A_B_F BetS_A_B_D Cong_B_F_B_D) as eq_F_D.
	assert (Cong A H D H) as Cong_A_H_D_H by (rewrite <- eq_F_D; exact Cong_A_H_F_H).

	pose proof (lemma_congruenceflip _ _ _ _ Cong_A_H_D_H) as (Cong_H_A_H_D & _ & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_A_H_D_H) as Cong_D_H_A_H.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_D_H_A_H) as (Cong_H_D_H_A & _ & _).

	(* assert by cases *)
	assert (eq C H \/ neq C H) as [eq_C_H|neq_C_H] by (apply Classical_Prop.classic).
	{
		(* case eq_C_H *)
		assert (Cong A C A H) as Cong_A_C_A_H by (rewrite <- eq_C_H; exact Cong_A_C_A_C).

		exact Cong_A_C_A_H.
	}
	(* case neq_C_H *)
	pose proof (proposition_10 _ _ neq_C_H) as (M & BetS_C_M_H & Cong_M_C_M_H).

	pose proof (cn_congruencereflexive C M) as Cong_C_M_C_M.
	pose proof (cn_congruencereflexive M H) as Cong_M_H_M_H.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_M_C_M_H) as (Cong_C_M_H_M & _ & _).

	(* assert by cases *)
	assert (eq B M \/ neq B M) as [eq_B_M|neq_B_M] by (apply Classical_Prop.classic).
	{
		(* case eq_B_M *)
		assert (BetS C B H) as BetS_C_B_H by (rewrite eq_B_M; exact BetS_C_M_H).
		pose proof (lemma_rightreverse _ _ _ _ RightTriangle_C_B_A BetS_C_B_H Cong_C_B_B_H) as Cong_C_A_H_A.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_C_A_H_A) as (Cong_A_C_A_H & _ & _).

		exact Cong_A_C_A_H.
	}
	(* case neq_B_M *)
	pose proof (lemma_inequalitysymmetric _ _ neq_B_M) as neq_M_B.

	pose proof (lemma_s_right_triangle _ _ _ _ BetS_C_M_H Cong_C_M_H_M Cong_C_B_H_B neq_M_B) as RightTriangle_C_M_B.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_C_M_B) as RightTriangle_B_M_C.

	(*
		Exterior triangles are △ACH and △DCH
		Shared interior sides are AM and DM.
	*)
	pose proof (
		lemma_interior5
		C M H A
		C M H D
		
		BetS_C_M_H
		BetS_C_M_H
		Cong_C_M_C_M
		Cong_M_H_M_H
		Cong_C_A_C_D
		Cong_H_A_H_D
	) as Cong_M_A_M_D.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_M_A_M_D) as (Cong_A_M_D_M & _ & _).

	pose proof (lemma_s_right_triangle _ _ _ _ BetS_A_B_D Cong_A_B_D_B Cong_A_M_D_M neq_B_M) as RightTriangle_A_B_M.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_A_B_M) as RightTriangle_M_B_A.

	(* Points C and A are reflected across line MB. *)
	pose proof (lemma_linereflectionisometry _ _ _ _ _ _ RightTriangle_B_M_C RightTriangle_M_B_A BetS_C_M_H BetS_A_B_D Cong_M_C_M_H Cong_B_A_B_D) as Cong_C_A_H_D.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_C_A_H_D) as (Cong_A_C_D_H & _ & _).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_C_A_H_D Cong_H_D_H_A) as Cong_C_A_H_A.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_C_A_H_A) as (Cong_A_C_A_H & _ & _).

	exact Cong_A_C_A_H.
Qed.

End Euclid.
