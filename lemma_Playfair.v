Require Import ProofCheckingEuclid.by_def_Cross.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Playfairhelper2.
Require Import ProofCheckingEuclid.lemma_crisscross.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_Playfair :
	forall A B C D E,
	Par A B C D ->
	Par A B C E ->
	Col C D E.
Proof.
	intros A B C D E.
	intros Par_AB_CD.
	intros Par_AB_CE.

	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_CD) as (Par_BA_CD & Par_AB_DC & Par_BA_DC).

	assert (Par_AB_CD_2 := Par_AB_CD).
	destruct Par_AB_CD_2 as (_ & _ & _ & _ & _ & neq_A_B & neq_C_D & _ & _ & _ & _ & _ & _ & n_Meet_A_B_C_D & _ & _).

	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_neq_symmetric _ _ neq_C_D) as neq_D_C.

	assert (~ ~ (Cross A D B C \/ Cross A C B D)) as n_n_Cross_AD_BC_or_Cross_AC_BD.
	{
		intro n_Cross_AD_BC_or_Cross_AC_BD.
		apply Classical_Prop.not_or_and in n_Cross_AD_BC_or_Cross_AC_BD.
		destruct n_Cross_AD_BC_or_Cross_AC_BD as (n_Cross_AD_BC & n_Cross_AC_BD).

		pose proof (lemma_crisscross _ _ _ _ Par_AB_DC n_Cross_AD_BC) as Cross_AC_DB.

		destruct Cross_AC_DB as (p & BetS_A_p_C & BetS_D_p_B).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_p_B) as BetS_B_p_D.

		pose proof (by_def_Cross _ _ _ _ _ BetS_A_p_C BetS_B_p_D) as Cross_AC_BD.

		contradict Cross_AC_BD.
		exact n_Cross_AC_BD.
	}
	assert (Cross_AD_BC_or_Cross_AC_BD := n_n_Cross_AD_BC_or_Cross_AC_BD).
	apply Classical_Prop.NNPP in Cross_AD_BC_or_Cross_AC_BD.

	(* assert by cases *)
	assert (Col C D E) as Col_C_D_E.
	destruct Cross_AD_BC_or_Cross_AC_BD as [Cross_AD_BC | Cross_AC_BD].
	{
		(* case Cross_AD_BC *)
		pose proof (lemma_Playfairhelper2 _ _ _ _ _ Par_AB_CD Par_AB_CE Cross_AD_BC) as Col_C_D_E.

		exact Col_C_D_E.
	}
	{
		(* case Cross_AC_BD *)

		destruct Cross_AC_BD as (p & BetS_A_p_C & BetS_B_p_D).

		pose proof (by_def_Cross _ _ _ _ _ BetS_B_p_D BetS_A_p_C) as Cross_BD_AC.
		pose proof (by_prop_Par_flip _ _ _ _ Par_AB_CE) as (Par_BA_CE & _ & _).

		pose proof (lemma_Playfairhelper2 _ _ _ _ _ Par_BA_CD Par_BA_CE Cross_BD_AC) as Col_C_D_E.

		exact Col_C_D_E.
	}

	exact Col_C_D_E.
Qed.

End Euclid.
