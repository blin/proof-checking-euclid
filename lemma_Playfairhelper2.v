Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Cross.
Require Import ProofCheckingEuclid.by_def_Par.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Playfairhelper.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_crisscross.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_Playfairhelper2 :
	forall A B C D E,
	Par A B C D ->
	Par A B C E ->
	Cross A D B C ->
	Col C D E.
Proof.
	intros A B C D E.
	intros Par_A_B_C_D.
	intros Par_A_B_C_E.
	intros Cross_A_D_B_C.

	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq E E) as eq_E_E by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C C E E eq_E_E) as Col_C_E_E.
	pose proof (by_def_Col_from_eq_A_B B B A eq_B_B) as Col_B_B_A.
	pose proof (by_def_Col_from_eq_A_C E C E eq_E_E) as Col_E_C_E.
	
	pose proof (by_prop_Par_flip _ _ _ _ Par_A_B_C_D) as (Par_B_A_C_D & Par_A_B_D_C & Par_B_A_D_C).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_A_B_C_D) as Par_C_D_A_B.
	pose proof (by_prop_Par_flip _ _ _ _ Par_C_D_A_B) as (Par_D_C_A_B & Par_C_D_B_A & Par_D_C_B_A).
	pose proof (by_prop_Par_NC _ _ _ _ Par_A_B_C_D) as (nCol_A_B_C & nCol_A_C_D & nCol_B_C_D & nCol_A_B_D).

	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (_ & nCol_B_C_A & _ & _ & _).
	
	assert (Par_A_B_C_D_2 := Par_A_B_C_D).
	destruct Par_A_B_C_D_2 as (_ & _ & _ & _ & _ & neq_A_B & neq_C_D & _ & _ & _ & _ & _ & _ & n_Meet_A_B_C_D & _ & _).
	
	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_neq_symmetric _ _ neq_C_D) as neq_D_C.

	pose proof (by_prop_Par_flip _ _ _ _ Par_A_B_C_E) as (Par_B_A_C_E & Par_A_B_E_C & Par_B_A_E_C).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_A_B_C_E) as Par_C_E_A_B.
	pose proof (by_prop_Par_flip _ _ _ _ Par_C_E_A_B) as (Par_E_C_A_B & Par_C_E_B_A & Par_E_C_B_A).
	pose proof (by_prop_Par_NC _ _ _ _ Par_A_B_C_E) as (_ & nCol_A_C_E & nCol_B_C_E & nCol_A_B_E).
	
	assert (Par_A_B_C_E_2 := Par_A_B_C_E).
	destruct Par_A_B_C_E_2 as (_ & _ & _ & _ & _ & _ & neq_C_E & _ & _ & _ & _ & _ & _ & n_Meet_A_B_C_E & _ & _).
	
	pose proof (by_prop_neq_symmetric _ _ neq_C_E) as neq_E_C.

	assert (~ ~ (Cross A E B C \/ Cross A C E B)) as n_n_Cross_A_E_B_C_or_Cross_A_C_E_B.
	{
		intro n_Cross_A_E_B_C_or_Cross_A_C_E_B.
		apply Classical_Prop.not_or_and in n_Cross_A_E_B_C_or_Cross_A_C_E_B.
		destruct n_Cross_A_E_B_C_or_Cross_A_C_E_B as (n_Cross_A_E_B_C & n_Cross_A_C_E_B).

		pose proof (lemma_crisscross _ _ _ _ Par_A_B_E_C n_Cross_A_E_B_C) as Cross_A_C_E_B.

		contradict Cross_A_C_E_B.
		exact n_Cross_A_C_E_B.
	}
	assert (Cross_A_E_B_C_or_Cross_A_C_E_B := n_n_Cross_A_E_B_C_or_Cross_A_C_E_B).
	apply Classical_Prop.NNPP in Cross_A_E_B_C_or_Cross_A_C_E_B.


	assert (Cross_A_D_B_C_2 := Cross_A_D_B_C).
	destruct Cross_A_D_B_C_2 as (M & BetS_A_M_D & BetS_B_M_C).

	(* assert by cases *)
	assert (Col C D E) as Col_C_D_E.
	destruct Cross_A_E_B_C_or_Cross_A_C_E_B as [Cross_A_E_B_C | Cross_A_C_E_B].
	{
		(* case Cross_A_E_B_C *)
		pose proof (lemma_Playfairhelper _ _ _ _ _ Par_A_B_C_D Par_A_B_C_E Cross_A_D_B_C Cross_A_E_B_C) as Col_C_D_E.

		exact Col_C_D_E.
	}
	{
		(* case Cross_A_C_E_B *)

		destruct Cross_A_C_E_B as (m & BetS_A_m_C & BetS_E_m_B).
			
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_m_B) as BetS_B_m_E.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_E_m_B) as (neq_m_B & neq_E_m & neq_E_B).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_B_m_E) as (neq_m_E & neq_B_m & neq_B_E).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_m_B) as Col_E_m_B.
		pose proof (by_prop_Col_order _ _ _ Col_E_m_B) as (Col_m_E_B & Col_m_B_E & Col_B_E_m & Col_E_B_m & Col_B_m_E).

		pose proof (lemma_extension E C E C neq_E_C neq_E_C) as (e & BetS_E_C_e & Cong_C_e_E_C).

		pose proof (by_def_Col_from_eq_B_C e E E eq_E_E) as Col_e_E_E.
		
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_C_e) as BetS_e_C_E.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_E_C_e) as (neq_C_e & _ & neq_E_e).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_e_C_E) as (_ & neq_e_C & neq_e_E).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_C_e) as Col_E_C_e.
		pose proof (by_prop_Col_order _ _ _ Col_E_C_e) as (Col_C_E_e & Col_C_e_E & Col_e_E_C & Col_E_e_C & Col_e_C_E).

		pose proof (by_prop_Par_collinear _ _ _ _ _ Par_A_B_E_C Col_E_C_e neq_e_C) as Par_A_B_e_C.
		pose proof (by_prop_Par_flip _ _ _ _ Par_A_B_e_C) as (Par_B_A_e_C & Par_A_B_C_e & Par_B_A_C_e).
		pose proof (by_prop_Par_symmetric _ _ _ _ Par_A_B_e_C) as Par_e_C_A_B.
		pose proof (by_prop_Par_flip _ _ _ _ Par_e_C_A_B) as (Par_C_e_A_B & Par_e_C_B_A & Par_C_e_B_A).
		pose proof (by_prop_Par_NC _ _ _ _ Par_A_B_e_C) as (nCol_A_B_e & nCol_A_e_C & nCol_B_e_C &_ ).

		pose proof (by_prop_Par_NC _ _ _ _ Par_A_B_E_C) as (_ & nCol_A_E_C & _ & _).
		pose proof (by_prop_nCol_order _ _ _ nCol_A_E_C) as (_ & _ & _ & _ & nCol_C_E_A).

		pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_C_E_A Col_C_E_E Col_C_E_e neq_E_e) as nCol_E_e_A.

		pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_A_m_C BetS_E_C_e nCol_E_e_A) as (F & BetS_A_F_e & BetS_E_m_F).
		
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_F_e) as BetS_e_F_A.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_A_F_e) as (neq_F_e & neq_A_F & neq_A_e).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_e_F_A) as (neq_F_A & neq_e_F & neq_e_A).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_F_e) as Col_A_F_e.
		pose proof (by_prop_Col_order _ _ _ Col_A_F_e) as (Col_F_A_e & Col_F_e_A & Col_e_A_F & Col_A_e_F & Col_e_F_A).

		pose proof (by_def_Col_from_BetS_A_B_C E m F BetS_E_m_F) as Col_E_m_F.
		pose proof (by_prop_Col_order _ _ _ Col_E_m_F) as (Col_m_E_F & _ & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_m_E_F Col_m_E_B neq_m_E) as Col_E_F_B.
		pose proof (by_prop_Col_order _ _ _ Col_E_F_B) as (_ & _ & _ & Col_E_B_F & _).

		pose proof (by_prop_Par_collinear _ _ _ _ _ Par_A_B_C_E Col_C_E_e neq_e_E) as Par_A_B_e_E.
		pose proof (by_prop_Par_symmetric _ _ _ _ Par_A_B_e_E) as Par_e_E_A_B.
		pose proof (by_prop_Par_flip _ _ _ _ Par_e_E_A_B) as (_ & Par_e_E_B_A & _).
		
		assert (Par_e_E_B_A_2 := Par_e_E_B_A).
		destruct Par_e_E_B_A_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_e_E_B_A & _ & _).

		pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_e_E_E Col_B_B_A neq_e_E neq_B_A neq_e_E neq_B_A n_Meet_e_E_B_A BetS_e_F_A Col_E_B_F) as BetS_E_F_B.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_F_B) as BetS_B_F_E.

		pose proof (by_prop_Par_NC _ _ _ _ Par_A_B_E_C) as (_ & _ & nCol_B_E_C & _).
		pose proof (by_prop_nCol_order _ _ _ nCol_B_E_C) as (_ & nCol_E_C_B & _ & _ & _).
		pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_E_C_B Col_E_C_E Col_E_C_e neq_E_e) as nCol_E_e_B.
		pose proof (by_prop_nCol_order _ _ _ nCol_E_e_B) as (_ & _ & nCol_B_E_e & _ & _).

		pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_B_F_E BetS_e_C_E nCol_B_E_e) as (K & BetS_B_K_C & BetS_e_K_F).

		pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_e_K_F BetS_e_F_A) as BetS_e_K_A.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_e_K_A) as BetS_A_K_e.
		pose proof (by_def_Cross _ _ _ _ _ BetS_A_K_e BetS_B_K_C) as Cross_A_e_B_C.

		pose proof (lemma_Playfairhelper _ _ _ _ _ Par_A_B_C_D Par_A_B_C_e Cross_A_D_B_C Cross_A_e_B_C) as Col_C_D_e.

		pose proof (by_prop_Col_order _ _ _ Col_C_D_e) as (_ & _ & Col_e_C_D & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_e_C_D Col_e_C_E neq_e_C) as Col_C_D_E.

		exact Col_C_D_E.
	}

	exact Col_C_D_E.
Qed.

End Euclid.

