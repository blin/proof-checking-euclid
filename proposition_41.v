Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_EqAreaTri_reflexive.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.proposition_37.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_41 :
	forall A B C D E,
	Parallelogram A B C D ->
	Col A D E ->
	EqAreaTri A B C E B C.
Proof.
	intros A B C D E.
	intros Parallelogram_A_B_C_D.
	intros Col_A_D_E.

	assert (Parallelogram_A_B_C_D_2 := Parallelogram_A_B_C_D).
	destruct Parallelogram_A_B_C_D_2 as (Par_AB_CD & Par_AD_BC).

	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (nCol_A_B_C & _ & _ & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AD_BC) as Par_BC_AD.
	pose proof (by_prop_Par_flip _ _ _ _ Par_BC_AD) as (_ & Par_BC_DA & _).
	pose proof (by_def_Triangle _ _ _ nCol_A_B_C) as Triangle_ABC.
	pose proof (by_prop_EqAreaTri_reflexive _ _ _ Triangle_ABC) as EqAreaTri_A_B_C_A_B_C.

	pose proof (by_prop_Col_order _ _ _ Col_A_D_E) as (Col_D_A_E & _ & _ & _ & _).

	(* assert by cases *)
	assert (EqAreaTri A B C E B C) as EqAreaTri_A_B_C_E_B_C.
	assert (eq A E \/ neq A E) as [eq_A_E|neq_A_E] by (apply Classical_Prop.classic).
	{
		(* case eq_A_E *)
		assert (EqAreaTri A B C E B C) as EqAreaTri_A_B_C_E_B_C by (rewrite <- eq_A_E; exact EqAreaTri_A_B_C_A_B_C).

		exact EqAreaTri_A_B_C_E_B_C.
	}
	{
		(* case neq_A_E *)
		pose proof (by_prop_neq_symmetric _ _ neq_A_E) as neq_E_A.
		pose proof (by_prop_Par_collinear _ _ _ _ _ Par_BC_DA Col_D_A_E neq_E_A) as Par_BC_EA.
		pose proof (by_prop_Par_flip _ _ _ _ Par_BC_EA) as (_ & Par_BC_AE & _).
		pose proof (by_prop_Par_symmetric _ _ _ _ Par_BC_AE) as Par_AE_BC.
		pose proof (proposition_37 _ _ _ _ Par_AE_BC) as EqAreaTri_A_B_C_E_B_C.

		exact EqAreaTri_A_B_C_E_B_C.
	}

	exact EqAreaTri_A_B_C_E_B_C.
Qed.

End Euclid.
