Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_s_meet.
Require Import ProofCheckingEuclid.lemma_s_tarski_par.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_tarskiparallelflip :
	forall A B C D,
	TarskiPar A B C D ->
	TarskiPar B A C D /\ TarskiPar A B D C /\ TarskiPar B A D C.
Proof.
	intros A B C D.
	intros TarskiPar_A_B_C_D.


	destruct TarskiPar_A_B_C_D as (neq_A_B & neq_C_D & n_Meet_A_B_C_D & SS_C_D_A_B).
	pose proof (lemma_samesidesymmetric _ _ _ _ SS_C_D_A_B) as (SS_D_C_A_B & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_C_D) as neq_D_C.

	assert (~ Meet A B D C) as n_Meet_A_B_D_C.
	{
		intro Meet_A_B_D_C.

		destruct Meet_A_B_D_C as (T & _ & _ & Col_A_B_T & Col_D_C_T).
		pose proof (lemma_collinearorder _ _ _ Col_D_C_T) as (Col_C_D_T & _ & _ & _ & _).
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_T Col_C_D_T) as Meet_A_B_C_D.
		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}
	pose proof (lemma_s_tarski_par _ _ _ _ neq_A_B neq_D_C n_Meet_A_B_D_C SS_D_C_A_B) as TarskiPar_A_B_D_C.

	assert (~ Meet B A C D) as n_Meet_B_A_C_D.
	{
		intro Meet_B_A_C_D.

		destruct Meet_B_A_C_D as (T & neq_B_A & _ & Col_B_A_T & Col_C_D_T).
		pose proof (lemma_collinearorder _ _ _ Col_B_A_T) as (Col_A_B_T & _ & _ & _ & _).
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_T Col_C_D_T) as Meet_A_B_C_D.
		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.
	pose proof (lemma_samesidesymmetric _ _ _ _ SS_C_D_A_B) as (_ & SS_C_D_B_A & _).
	pose proof (lemma_samesidesymmetric _ _ _ _ SS_C_D_B_A) as (SS_D_C_B_A & _ & _).

	pose proof (lemma_s_tarski_par _ _ _ _ neq_B_A neq_C_D n_Meet_B_A_C_D SS_C_D_B_A) as TarskiPar_B_A_C_D.

	assert (~ Meet B A D C) as n_Meet_B_A_D_C.
	{
		intro Meet_B_A_D_C.

		destruct Meet_B_A_D_C as (T & _ & _ & Col_B_A_T & Col_D_C_T).
		pose proof (lemma_collinearorder _ _ _ Col_B_A_T) as (Col_A_B_T & _ & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_D_C_T) as (Col_C_D_T & _ & _ & _ & _).
		pose proof (lemma_s_meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_T Col_C_D_T) as Meet_A_B_C_D.
		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	pose proof (lemma_s_tarski_par _ _ _ _ neq_B_A neq_D_C n_Meet_B_A_D_C SS_D_C_B_A) as TarskiPar_B_A_D_C.

	split.
	exact TarskiPar_B_A_C_D.
	split.
	exact TarskiPar_A_B_D_C.
	exact TarskiPar_B_A_D_C.
Qed.

End Euclid.
