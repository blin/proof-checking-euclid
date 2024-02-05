Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Cross.
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
	intros Par_AB_CD.
	intros Par_AB_CE.
	intros Cross_AD_BC.

	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq E E) as eq_E_E by (reflexivity).
	pose proof (by_def_Col_from_eq_A_B B B A eq_B_B) as Col_B_B_A.
	pose proof (by_def_Col_from_eq_A_C E C E eq_E_E) as Col_E_C_E.
	pose proof (by_def_Col_from_eq_B_C C E E eq_E_E) as Col_C_E_E.

	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_CD) as (Par_BA_CD & Par_AB_DC & Par_BA_DC).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AB_CD) as Par_CD_AB.
	pose proof (by_prop_Par_flip _ _ _ _ Par_CD_AB) as (Par_DC_AB & Par_CD_BA & Par_DC_BA).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (nCol_A_B_C & nCol_A_C_D & nCol_B_C_D & nCol_A_B_D).

	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (_ & nCol_B_C_A & _ & _ & _).

	assert (Par_AB_CD_2 := Par_AB_CD).
	destruct Par_AB_CD_2 as (_ & _ & _ & _ & _ & neq_A_B & neq_C_D & _ & _ & _ & _ & _ & _ & n_Meet_A_B_C_D & _ & _).

	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.

	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_CE) as (Par_BA_CE & Par_AB_EC & Par_BA_EC).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AB_CE) as Par_CE_AB.
	pose proof (by_prop_Par_flip _ _ _ _ Par_CE_AB) as (Par_EC_AB & Par_CE_BA & Par_EC_BA).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CE) as (_ & nCol_A_C_E & nCol_B_C_E & nCol_A_B_E).

	assert (Par_AB_CE_2 := Par_AB_CE).
	destruct Par_AB_CE_2 as (_ & _ & _ & _ & _ & _ & neq_C_E & _ & _ & _ & _ & _ & _ & n_Meet_A_B_C_E & _ & _).

	pose proof (by_prop_neq_symmetric _ _ neq_C_E) as neq_E_C.

	assert (~ ~ (Cross A E B C \/ Cross A C E B)) as n_n_Cross_AE_BC_or_Cross_AC_EB.
	{
		intro n_Cross_AE_BC_or_Cross_AC_EB.
		apply Classical_Prop.not_or_and in n_Cross_AE_BC_or_Cross_AC_EB.
		destruct n_Cross_AE_BC_or_Cross_AC_EB as (n_Cross_AE_BC & n_Cross_AC_EB).

		pose proof (lemma_crisscross _ _ _ _ Par_AB_EC n_Cross_AE_BC) as Cross_AC_EB.

		contradict Cross_AC_EB.
		exact n_Cross_AC_EB.
	}
	assert (Cross_AE_BC_or_Cross_AC_EB := n_n_Cross_AE_BC_or_Cross_AC_EB).
	apply Classical_Prop.NNPP in Cross_AE_BC_or_Cross_AC_EB.

	(* assert by cases *)
	assert (Col C D E) as Col_C_D_E.
	destruct Cross_AE_BC_or_Cross_AC_EB as [Cross_AE_BC | Cross_AC_EB].
	{
		(* case Cross_AE_BC *)
		pose proof (lemma_Playfairhelper _ _ _ _ _ Par_AB_CD Par_AB_CE Cross_AD_BC Cross_AE_BC) as Col_C_D_E.

		exact Col_C_D_E.
	}
	{
		(* case Cross_AC_EB *)

		destruct Cross_AC_EB as (m & BetS_A_m_C & BetS_E_m_B).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_m_B) as BetS_B_m_E.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_E_m_B) as (neq_m_B & neq_E_m & neq_E_B).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_B_m_E) as (neq_m_E & neq_B_m & neq_B_E).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_m_B) as Col_E_m_B.
		pose proof (by_prop_Col_order _ _ _ Col_E_m_B) as (Col_m_E_B & Col_m_B_E & Col_B_E_m & Col_E_B_m & Col_B_m_E).

		pose proof (lemma_extension _ _ _ _ neq_E_C neq_E_C) as (e & BetS_E_C_e & Cong_Ce_EC).

		pose proof (by_def_Col_from_eq_B_C e E E eq_E_E) as Col_e_E_E.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_C_e) as BetS_e_C_E.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_E_C_e) as (neq_C_e & _ & neq_E_e).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_e_C_E) as (_ & neq_e_C & neq_e_E).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_C_e) as Col_E_C_e.
		pose proof (by_prop_Col_order _ _ _ Col_E_C_e) as (Col_C_E_e & Col_C_e_E & Col_e_E_C & Col_E_e_C & Col_e_C_E).

		pose proof (by_prop_Par_collinear _ _ _ _ _ Par_AB_EC Col_E_C_e neq_e_C) as Par_AB_eC.
		pose proof (by_prop_Par_flip _ _ _ _ Par_AB_eC) as (Par_BA_eC & Par_AB_Ce & Par_BA_Ce).
		pose proof (by_prop_Par_symmetric _ _ _ _ Par_AB_eC) as Par_eC_AB.
		pose proof (by_prop_Par_flip _ _ _ _ Par_eC_AB) as (Par_Ce_AB & Par_eC_BA & Par_Ce_BA).
		pose proof (by_prop_Par_NC _ _ _ _ Par_AB_eC) as (nCol_A_B_e & nCol_A_e_C & nCol_B_e_C &_ ).

		pose proof (by_prop_Par_NC _ _ _ _ Par_AB_EC) as (_ & nCol_A_E_C & _ & _).
		pose proof (by_prop_nCol_order _ _ _ nCol_A_E_C) as (_ & _ & _ & _ & nCol_C_E_A).

		pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_C_E_A Col_C_E_E Col_C_E_e neq_E_e) as nCol_E_e_A.

		pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_A_m_C BetS_E_C_e nCol_E_e_A) as (F & BetS_A_F_e & BetS_E_m_F).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_F_e) as BetS_e_F_A.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_A_F_e) as (neq_F_e & neq_A_F & neq_A_e).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_e_F_A) as (neq_F_A & neq_e_F & neq_e_A).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_F_e) as Col_A_F_e.
		pose proof (by_prop_Col_order _ _ _ Col_A_F_e) as (Col_F_A_e & Col_F_e_A & Col_e_A_F & Col_A_e_F & Col_e_F_A).

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_m_F) as Col_E_m_F.
		pose proof (by_prop_Col_order _ _ _ Col_E_m_F) as (Col_m_E_F & _ & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_m_E_F Col_m_E_B neq_m_E) as Col_E_F_B.
		pose proof (by_prop_Col_order _ _ _ Col_E_F_B) as (_ & _ & _ & Col_E_B_F & _).

		pose proof (by_prop_Par_collinear _ _ _ _ _ Par_AB_CE Col_C_E_e neq_e_E) as Par_AB_eE.
		pose proof (by_prop_Par_symmetric _ _ _ _ Par_AB_eE) as Par_eE_AB.
		pose proof (by_prop_Par_flip _ _ _ _ Par_eE_AB) as (_ & Par_eE_BA & _).

		assert (Par_eE_BA_2 := Par_eE_BA).
		destruct Par_eE_BA_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_e_E_B_A & _ & _).

		pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_e_E_E Col_B_B_A neq_e_E neq_B_A neq_e_E neq_B_A n_Meet_e_E_B_A BetS_e_F_A Col_E_B_F) as BetS_E_F_B.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_F_B) as BetS_B_F_E.

		pose proof (by_prop_Par_NC _ _ _ _ Par_AB_EC) as (_ & _ & nCol_B_E_C & _).
		pose proof (by_prop_nCol_order _ _ _ nCol_B_E_C) as (_ & nCol_E_C_B & _ & _ & _).
		pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_E_C_B Col_E_C_E Col_E_C_e neq_E_e) as nCol_E_e_B.
		pose proof (by_prop_nCol_order _ _ _ nCol_E_e_B) as (_ & _ & nCol_B_E_e & _ & _).

		pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_B_F_E BetS_e_C_E nCol_B_E_e) as (K & BetS_B_K_C & BetS_e_K_F).

		pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_e_K_F BetS_e_F_A) as BetS_e_K_A.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_e_K_A) as BetS_A_K_e.
		pose proof (by_def_Cross _ _ _ _ _ BetS_A_K_e BetS_B_K_C) as Cross_Ae_BC.

		pose proof (lemma_Playfairhelper _ _ _ _ _ Par_AB_CD Par_AB_Ce Cross_AD_BC Cross_Ae_BC) as Col_C_D_e.

		pose proof (by_prop_Col_order _ _ _ Col_C_D_e) as (_ & _ & Col_e_C_D & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_e_C_D Col_e_C_E neq_e_C) as Col_C_D_E.

		exact Col_C_D_E.
	}

	exact Col_C_D_E.
Qed.

End Euclid.
