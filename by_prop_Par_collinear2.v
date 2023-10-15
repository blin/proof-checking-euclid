Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct .
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_Par_collinear2 :
	forall A B C D E F,
	Par A B C D ->
	Col C D E ->
	Col C D F ->
	neq E F ->
	Par A B E F.
Proof.
	intros A B C D E F.
	intros Par_AB_CD.
	intros Col_C_D_E.
	intros Col_C_D_F.
	intros neq_E_F.

	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_CD) as (Par_BA_CD & Par_AB_DC & Par_BA_DC).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (nCol_A_B_C & nCol_A_C_D & nCol_B_C_D & nCol_A_B_D).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_C_D) as (neq_B_C & neq_C_D & neq_B_D & neq_C_B & neq_D_C & neq_D_B).

	pose proof (by_prop_Col_order _ _ _ Col_C_D_E) as (Col_D_C_E & Col_D_E_C & Col_E_C_D & Col_C_E_D & Col_E_D_C).
	pose proof (by_prop_Col_order _ _ _ Col_C_D_F) as (Col_D_C_F & Col_D_F_C & Col_F_C_D & Col_C_F_D & Col_F_D_C).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_D_E Col_C_D_F neq_C_D) as Col_D_E_F.

	pose proof (by_prop_neq_symmetric _ _ neq_E_F) as neq_F_E.

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_C_E Col_D_C_F neq_D_C) as Col_C_E_F.
	pose proof (by_prop_Col_order _ _ _ Col_C_E_F) as (_ & _ & _ & Col_C_F_E & _).


	(* assert by cases *)
	assert (Par A B E F) as Par_AB_EF.
	assert (eq E D \/ neq E D) as [eq_E_D|neq_E_D] by (apply Classical_Prop.classic).
	{
		(* case eq_E_D *)
		assert (neq D F) as neq_D_F by (rewrite <- eq_E_D; exact neq_E_F).
		pose proof (by_prop_neq_symmetric _ _ neq_D_F) as neq_F_D.

		pose proof (by_prop_Par_collinear _ _ _ _ _ Par_AB_CD Col_C_D_F neq_F_D) as Par_AB_FD.
		pose proof (by_prop_Par_flip _ _ _ _ Par_AB_FD) as (_ & Par_AB_DF & _).

		(* assert by cases *)
		assert (Col F D E) as Col_F_D_E.
		assert (eq C F \/ neq C F) as [eq_C_F|neq_C_F] by (apply Classical_Prop.classic).
		{
			(* case eq_C_F *)
			assert (Col F D E) as Col_F_D_E by (rewrite <- eq_C_F; exact Col_C_D_E).

			exact Col_F_D_E.
		}
		{
			(* case neq_C_F *)
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_F_D Col_C_F_E neq_C_F) as Col_F_D_E.

			exact Col_F_D_E.
		}
		pose proof (by_prop_Col_order _ _ _ Col_F_D_E) as (Col_D_F_E & _ & _ & _ & _).

		pose proof (by_prop_Par_collinear _ _ _ _ _ Par_AB_DF Col_D_F_E neq_E_F) as Par_AB_EF.

		exact Par_AB_EF.
	}
	{
		(* case neq_E_D *)
		pose proof (by_prop_Par_collinear _ _ _ _ _ Par_AB_CD Col_C_D_E neq_E_D) as Par_AB_ED.
		pose proof (by_prop_Par_flip _ _ _ _ Par_AB_ED) as (_ & Par_AB_DE & _).
		pose proof (by_prop_Par_collinear _ _ _ _ _ Par_AB_DE Col_D_E_F neq_F_E) as Par_AB_FE.
		pose proof (by_prop_Par_flip _ _ _ _ Par_AB_FE) as (_ & Par_AB_EF & _).

		exact Par_AB_EF.
	}

	exact Par_AB_EF.
Qed.

End Euclid.
