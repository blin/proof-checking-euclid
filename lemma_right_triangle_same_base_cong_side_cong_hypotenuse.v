Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
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
Require Import ProofCheckingEuclid.lemma_s_right_triangle.
Require Import ProofCheckingEuclid.proposition_10.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

(*
	There are three notable scenarios here.
	1. SS C H A B
	2. OS C A B H
	3. ~ SS C H A B /\ ~ OS C A B H -> A B C H are not in the same plane.
*)
Lemma lemma_right_triangle_same_base_cong_side_cong_hypotenuse :
	forall A B C H,
	RightTriangle A B C ->
	RightTriangle A B H ->
	Cong B C B H ->
	Cong A C A H.
Proof.
	intros A B C H.
	intros RightTriangle_ABC.
	intros RightTriangle_ABH.
	intros Cong_BC_BH.

	pose proof (cn_congruencereflexive A C) as Cong_AC_AC.

	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_ABC) as RightTriangle_CBA.

	assert (RightTriangle_ABC2 := RightTriangle_ABC).
	destruct RightTriangle_ABC2 as (D & BetS_A_B_D & Cong_AB_DB & Cong_AC_DC & _).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AB_DB) as Cong_DB_AB.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AC_DC) as (Cong_CA_CD & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AB_DB) as (Cong_BA_BD & _ & _).

	assert (RightTriangle_ABH2 := RightTriangle_ABH).
	destruct RightTriangle_ABH2 as (F & BetS_A_B_F & Cong_AB_FB & Cong_AH_FH & _).

	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_DB_AB Cong_AB_FB) as Cong_DB_FB.
	pose proof (lemma_doublereverse _ _ _ _ Cong_DB_FB) as (Cong_BF_BD & _).

	pose proof (lemma_doublereverse _ _ _ _ Cong_BC_BH) as (_ & Cong_CB_HB).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_BC_BH) as (_ & Cong_CB_BH & _).

	pose proof (lemma_extensionunique _ _ _ _ BetS_A_B_F BetS_A_B_D Cong_BF_BD) as eq_F_D.
	assert (Cong A H D H) as Cong_AH_DH by (rewrite <- eq_F_D; exact Cong_AH_FH).

	pose proof (lemma_congruenceflip _ _ _ _ Cong_AH_DH) as (Cong_HA_HD & _ & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AH_DH) as Cong_DH_AH.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_DH_AH) as (Cong_HD_HA & _ & _).

	(* assert by cases *)
	assert (eq C H \/ neq C H) as [eq_C_H|neq_C_H] by (apply Classical_Prop.classic).
	{
		(* case eq_C_H *)
		assert (Cong A C A H) as Cong_AC_AH by (rewrite <- eq_C_H; exact Cong_AC_AC).

		exact Cong_AC_AH.
	}
	(* case neq_C_H *)
	pose proof (proposition_10 _ _ neq_C_H) as (M & BetS_C_M_H & Cong_MC_MH).

	pose proof (cn_congruencereflexive C M) as Cong_CM_CM.
	pose proof (cn_congruencereflexive M H) as Cong_MH_MH.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_MC_MH) as (Cong_CM_HM & _ & _).

	(* assert by cases *)
	assert (eq B M \/ neq B M) as [eq_B_M|neq_B_M] by (apply Classical_Prop.classic).
	{
		(* case eq_B_M *)
		assert (BetS C B H) as BetS_C_B_H by (rewrite eq_B_M; exact BetS_C_M_H).
		pose proof (lemma_rightreverse _ _ _ _ RightTriangle_CBA BetS_C_B_H Cong_CB_BH) as Cong_CA_HA.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_CA_HA) as (Cong_AC_AH & _ & _).

		exact Cong_AC_AH.
	}
	(* case neq_B_M *)
	pose proof (lemma_inequalitysymmetric _ _ neq_B_M) as neq_M_B.

	pose proof (lemma_s_right_triangle _ _ _ _ BetS_C_M_H Cong_CM_HM Cong_CB_HB neq_M_B) as RightTriangle_CMB.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_CMB) as RightTriangle_BMC.

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
		Cong_CM_CM
		Cong_MH_MH
		Cong_CA_CD
		Cong_HA_HD
	) as Cong_MA_MD.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_MA_MD) as (Cong_AM_DM & _ & _).

	pose proof (lemma_s_right_triangle _ _ _ _ BetS_A_B_D Cong_AB_DB Cong_AM_DM neq_B_M) as RightTriangle_ABM.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_ABM) as RightTriangle_MBA.

	(* Points C and A are reflected across line MB. *)
	pose proof (lemma_linereflectionisometry _ _ _ _ _ _ RightTriangle_BMC RightTriangle_MBA BetS_C_M_H BetS_A_B_D Cong_MC_MH Cong_BA_BD) as Cong_CA_HD.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_CA_HD) as (Cong_AC_DH & _ & _).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_CA_HD Cong_HD_HA) as Cong_CA_HA.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_CA_HA) as (Cong_AC_AH & _ & _).

	exact Cong_AC_AH.
Qed.

End Euclid.
