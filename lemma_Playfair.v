Require Import ProofCheckingEuclid.by_def_Cross.
Require Import ProofCheckingEuclid.by_def_Par.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
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
	intros Par_A_B_C_D.
	intros Par_A_B_C_E.
	
	pose proof (by_prop_Par_flip _ _ _ _ Par_A_B_C_D) as (Par_B_A_C_D & Par_A_B_D_C & Par_B_A_D_C).
	
	assert (Par_A_B_C_D_2 := Par_A_B_C_D).
	destruct Par_A_B_C_D_2 as (_ & _ & _ & _ & _ & neq_A_B & neq_C_D & _ & _ & _ & _ & _ & _ & n_Meet_A_B_C_D & _ & _).
	
	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_neq_symmetric _ _ neq_C_D) as neq_D_C.

	assert (~ ~ (Cross A D B C \/ Cross A C B D)) as n_n_Cross_A_D_B_C_or_Cross_A_C_B_D.
	{
		intro n_Cross_A_D_B_C_or_Cross_A_C_B_D.
		apply Classical_Prop.not_or_and in n_Cross_A_D_B_C_or_Cross_A_C_B_D.
		destruct n_Cross_A_D_B_C_or_Cross_A_C_B_D as (n_Cross_A_D_B_C & n_Cross_A_C_B_D).

		pose proof (lemma_crisscross _ _ _ _ Par_A_B_D_C n_Cross_A_D_B_C) as Cross_A_C_D_B.

		destruct Cross_A_C_D_B as (p & BetS_A_p_C & BetS_D_p_B).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_D_p_B) as (_ & _ & neq_D_B).
		pose proof (by_prop_neq_symmetric _ _ neq_D_B) as neq_B_D.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_p_B) as BetS_B_p_D.
		pose proof (by_def_Cross _ _ _ _ _ BetS_A_p_C BetS_B_p_D) as Cross_A_C_B_D.

		contradict Cross_A_C_B_D.
		exact n_Cross_A_C_B_D.
	}
	assert (Cross_A_D_B_C_or_Cross_A_C_B_D := n_n_Cross_A_D_B_C_or_Cross_A_C_B_D).
	apply Classical_Prop.NNPP in Cross_A_D_B_C_or_Cross_A_C_B_D.

	(* assert by cases *)
	assert (Col C D E) as Col_C_D_E.
	destruct Cross_A_D_B_C_or_Cross_A_C_B_D as [Cross_A_D_B_C | Cross_A_C_B_D].
	{
		(* case Cross_A_D_B_C *)
		pose proof (lemma_Playfairhelper2 _ _ _ _ _ Par_A_B_C_D Par_A_B_C_E Cross_A_D_B_C) as Col_C_D_E.

		exact Col_C_D_E.
	}
	{
		(* case Cross_A_C_B_D *)

		destruct Cross_A_C_B_D as (p & BetS_A_p_C & BetS_B_p_D).
		pose proof (by_def_Cross _ _ _ _ _ BetS_B_p_D BetS_A_p_C) as Cross_B_D_A_C.
		pose proof (by_prop_Par_flip _ _ _ _ Par_A_B_C_E) as (Par_B_A_C_E & _ & _).
		epose proof (lemma_Playfairhelper2 B A C D E Par_B_A_C_D Par_B_A_C_E Cross_B_D_A_C) as Col_C_D_E.

		exact Col_C_D_E.
	}

	exact Col_C_D_E.
Qed.

End Euclid.
