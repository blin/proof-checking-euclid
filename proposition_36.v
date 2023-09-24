Require Import ProofCheckingEuclid.by_def_Cross.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear2.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_crisscross.
Require Import ProofCheckingEuclid.proposition_33.
Require Import ProofCheckingEuclid.proposition_34.
Require Import ProofCheckingEuclid.proposition_35.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_36 :
	forall A B C D E F G H,
	Parallelogram A B C D ->
	Parallelogram E F G H ->
	Col A D E ->
	Col A D H ->
	Col B C F ->
	Col B C G ->
	Cong B C F G ->
	EqAreaQuad A B C D E F G H.
Proof.
	intros A B C D E F G H.
	intros Parallelogram_A_B_C_D.
	intros Parallelogram_E_F_G_H.
	intros Col_A_D_E.
	intros Col_A_D_H.
	intros Col_B_C_F.
	intros Col_B_C_G.
	intros Cong_B_C_F_G.

	assert (Parallelogram_A_B_C_D_2 := Parallelogram_A_B_C_D).
	destruct Parallelogram_A_B_C_D_2 as (Par_A_B_C_D & Par_A_D_B_C).
	
	assert (Parallelogram_E_F_G_H_2 := Parallelogram_E_F_G_H).
	destruct Parallelogram_E_F_G_H_2 as (Par_E_F_G_H & Par_E_H_F_G).
	
	pose proof (proposition_34 _ _ _ _ Parallelogram_E_F_G_H) as (Cong_E_H_F_G & Cong_E_F_H_G & CongA_F_E_H_H_G_F & CongA_E_H_G_G_F_E & CongTriangles_F_E_H_H_G_F).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_E_H_F_G) as Cong_F_G_E_H.
	
	pose proof (by_prop_Par_flip _ _ _ _ Par_A_B_C_D) as (Par_B_A_C_D & Par_A_B_D_C & Par_B_A_D_C).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_A_B_C_D) as Par_C_D_A_B.
	pose proof (by_prop_Par_flip _ _ _ _ Par_C_D_A_B) as (Par_D_C_A_B & Par_C_D_B_A & Par_D_C_B_A).
	pose proof (by_prop_Par_NC _ _ _ _ Par_A_B_C_D) as (nCol_A_B_C & nCol_A_C_D & nCol_B_C_D & nCol_A_B_D).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (_ & neq_B_C & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_B_C) as neq_C_B.

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_A_D_B_C) as Par_B_C_A_D.

	pose proof (by_prop_Par_flip _ _ _ _ Par_E_F_G_H) as (Par_F_E_G_H & Par_E_F_H_G & Par_F_E_H_G).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_E_F_G_H) as Par_G_H_E_F.
	pose proof (by_prop_Par_flip _ _ _ _ Par_G_H_E_F) as (Par_H_G_E_F & Par_G_H_F_E & Par_H_G_F_E).
	pose proof (by_prop_Par_NC _ _ _ _ Par_E_F_G_H) as (nCol_E_F_G & nCol_E_G_H & nCol_F_G_H & nCol_E_F_H).
	
	pose proof (by_prop_Par_flip _ _ _ _ Par_E_H_F_G) as (Par_H_E_F_G & Par_E_H_G_F & Par_H_E_G_F).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_E_H_F_G) as Par_F_G_E_H.
	pose proof (by_prop_Par_flip _ _ _ _ Par_F_G_E_H) as (Par_G_F_E_H & Par_F_G_H_E & Par_G_F_H_E).
	pose proof (by_prop_Par_NC _ _ _ _ Par_E_H_F_G) as (nCol_E_H_F & _ & nCol_H_F_G & nCol_E_H_G).
	
	pose proof (by_prop_nCol_distinct _ _ _ nCol_E_H_F) as (neq_E_H & neq_H_F & neq_E_F & neq_H_E & neq_F_H & neq_F_E).
	
	pose proof (by_prop_Col_order _ _ _ Col_B_C_F) as (Col_C_B_F & Col_C_F_B & Col_F_B_C & Col_B_F_C & Col_F_C_B).
	pose proof (by_prop_Col_order _ _ _ Col_B_C_G) as (Col_C_B_G & Col_C_G_B & Col_G_B_C & Col_B_G_C & Col_G_C_B).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_C_F Col_B_C_G neq_B_C) as Col_C_F_G.
	pose proof (by_prop_Col_order _ _ _ Col_C_F_G) as (_ & _ & _ & _ & Col_G_F_C).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_B_F Col_C_B_G neq_C_B) as Col_B_F_G.
	pose proof (by_prop_Col_order _ _ _ Col_B_F_G) as (_ & _ & _ & _ & Col_G_F_B).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_C_G Col_B_C_F neq_B_C) as Col_C_G_F.
	pose proof (by_prop_Col_order _ _ _ Col_C_G_F) as (_ & _ & _ & _ & Col_F_G_C).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_B_G Col_C_B_F neq_C_B) as Col_B_G_F.
	pose proof (by_prop_Col_order _ _ _ Col_B_G_F) as (_ & _ & _ & _ & Col_F_G_B).

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_B_C_F_G Cong_F_G_E_H) as Cong_B_C_E_H.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_B_C_E_H) as Cong_E_H_B_C.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_E_H_B_C) as (_ & Cong_H_E_B_C & _).

	pose proof (by_prop_Par_collinear2 _ _ _ _ _ _ Par_B_C_A_D Col_A_D_E Col_A_D_H neq_E_H) as Par_B_C_E_H.
	pose proof (by_prop_Par_flip _ _ _ _ Par_B_C_E_H) as (Par_C_B_E_H & Par_B_C_H_E & Par_C_B_H_E).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_B_C_E_H) as Par_E_H_B_C.
	pose proof (by_prop_Par_flip _ _ _ _ Par_E_H_B_C) as (Par_H_E_B_C & Par_E_H_C_B & Par_H_E_C_B).
	pose proof (by_prop_Par_NC _ _ _ _ Par_B_C_E_H) as (nCol_B_C_E & nCol_B_E_H & nCol_C_E_H & nCol_B_C_H).

	pose proof (by_def_Parallelogram _ _ _ _ Par_G_H_E_F Par_G_F_H_E) as Parallelogram_G_H_E_F.
	pose proof (by_def_Parallelogram _ _ _ _ Par_F_E_H_G Par_F_G_E_H) as Parallelogram_F_E_H_G.
	
	assert (~ ~ (Cross E C B H \/ Cross E B H C)) as n_n_Cross_E_C_B_H_or_Cross_E_B_H_C.
	{
		intro n_Cross_E_C_B_H_or_Cross_E_B_H_C.
		
		apply Classical_Prop.not_or_and in n_Cross_E_C_B_H_or_Cross_E_B_H_C .
		destruct n_Cross_E_C_B_H_or_Cross_E_B_H_C as (n_Cross_E_C_B_H & n_Cross_E_B_H_C).

		pose proof (lemma_crisscross _ _ _ _ Par_E_H_B_C n_Cross_E_B_H_C) as Cross_E_C_B_H.

		contradict Cross_E_C_B_H.
		exact n_Cross_E_C_B_H.
	}
	assert (Cross_E_C_B_H_or_Cross_E_B_H_C := n_n_Cross_E_C_B_H_or_Cross_E_B_H_C).
	apply Classical_Prop.NNPP in Cross_E_C_B_H_or_Cross_E_B_H_C.


	(* assert by cases *)
	assert (EqAreaQuad A B C D E F G H) as EqAreaQuad_A_B_C_D_E_F_G_H.
	destruct Cross_E_C_B_H_or_Cross_E_B_H_C as [Cross_E_C_B_H | Cross_E_B_H_C].
	{
		(* case Cross_E_C_B_H *)

		destruct Cross_E_C_B_H as (M & BetS_E_M_C & BetS_B_M_H).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_H) as BetS_H_M_B.

		pose proof (proposition_33 _ _ _ _ _ Par_E_H_B_C Cong_E_H_B_C BetS_E_M_C BetS_H_M_B) as (Par_E_B_H_C & Cong_E_B_H_C).
		
		pose proof (by_prop_Par_flip _ _ _ _ Par_E_B_H_C) as (Par_B_E_H_C & Par_E_B_C_H & Par_B_E_C_H).
		pose proof (by_prop_Par_symmetric _ _ _ _ Par_E_B_H_C) as Par_H_C_E_B.
		pose proof (by_prop_Par_flip _ _ _ _ Par_H_C_E_B) as (Par_C_H_E_B & Par_H_C_B_E & Par_C_H_B_E).

		pose proof (by_def_Parallelogram _ _ _ _ Par_E_B_C_H Par_E_H_B_C) as Parallelogram_E_B_C_H.
		pose proof (by_def_Parallelogram _ _ _ _ Par_C_H_E_B Par_C_B_H_E) as Parallelogram_C_H_E_B.

		pose proof (proposition_35 _ _ _ _ _ _ Parallelogram_A_B_C_D Parallelogram_E_B_C_H Col_A_D_E Col_A_D_H) as EqAreaQuad_A_B_C_D_E_B_C_H.
		pose proof (proposition_35 _ _ _ _ _ _ Parallelogram_G_H_E_F Parallelogram_C_H_E_B Col_G_F_C Col_G_F_B) as EqAreaQuad_G_H_E_F_C_H_E_B.

		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_G_H_E_F_C_H_E_B) as (_ & _ & EqAreaQuad_G_H_E_F_E_B_C_H & _ & _ & _ & _).
		pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_G_H_E_F_E_B_C_H) as EqAreaQuad_E_B_C_H_G_H_E_F.
		pose proof (axiom_EqAreaQuad_transitive _ _ _ _ _ _ _ _ _ _ _ _ EqAreaQuad_A_B_C_D_E_B_C_H EqAreaQuad_E_B_C_H_G_H_E_F) as EqAreaQuad_A_B_C_D_G_H_E_F.
		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_A_B_C_D_G_H_E_F) as (_ & _ & EqAreaQuad_A_B_C_D_E_F_G_H & _ & _ & _ & _).

		exact EqAreaQuad_A_B_C_D_E_F_G_H.
	}
	{
		(* case Cross_E_B_H_C *)

		destruct Cross_E_B_H_C as (M & BetS_E_M_B & BetS_H_M_C).

		pose proof (proposition_33 _ _ _ _ _ Par_H_E_B_C Cong_H_E_B_C BetS_H_M_C BetS_E_M_B) as (Par_H_B_E_C & Cong_H_B_E_C).
		
		pose proof (by_prop_Par_flip _ _ _ _ Par_H_B_E_C) as (Par_B_H_E_C & Par_H_B_C_E & Par_B_H_C_E).
		pose proof (by_prop_Par_symmetric _ _ _ _ Par_H_B_E_C) as Par_E_C_H_B.
		pose proof (by_prop_Par_flip _ _ _ _ Par_E_C_H_B) as (Par_C_E_H_B & Par_E_C_B_H & Par_C_E_B_H).

		pose proof (by_def_Parallelogram _ _ _ _ Par_H_B_C_E Par_H_E_B_C) as Parallelogram_H_B_C_E.
		pose proof (by_def_Parallelogram _ _ _ _ Par_C_E_H_B Par_C_B_E_H) as Parallelogram_C_E_H_B.

		pose proof (proposition_35 _ _ _ _ _ _ Parallelogram_A_B_C_D Parallelogram_H_B_C_E Col_A_D_H Col_A_D_E) as EqAreaQuad_A_B_C_D_H_B_C_E.
		pose proof (proposition_35 _ _ _ _ _ _ Parallelogram_F_E_H_G Parallelogram_C_E_H_B Col_F_G_C Col_F_G_B) as EqAreaQuad_F_E_H_G_C_E_H_B.

		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_F_E_H_G_C_E_H_B) as (_ & _ & EqAreaQuad_F_E_H_G_H_B_C_E & _ & _ & _ & _).
		pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_F_E_H_G_H_B_C_E) as EqAreaQuad_H_B_C_E_F_E_H_G.
		pose proof (axiom_EqAreaQuad_transitive _ _ _ _ _ _ _ _ _ _ _ _ EqAreaQuad_A_B_C_D_H_B_C_E EqAreaQuad_H_B_C_E_F_E_H_G) as EqAreaQuad_A_B_C_D_F_E_H_G.
		pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_A_B_C_D_F_E_H_G) as (_ & _ & _ & EqAreaQuad_A_B_C_D_E_F_G_H & _ & _ & _).

		exact EqAreaQuad_A_B_C_D_E_F_G_H.
	}

	exact EqAreaQuad_A_B_C_D_E_F_G_H.
Qed.

End Euclid.
