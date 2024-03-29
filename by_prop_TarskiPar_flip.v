Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_TarskiPar_flip :
	forall A B C D,
	TarskiPar A B C D ->
	TarskiPar B A C D /\ TarskiPar A B D C /\ TarskiPar B A D C.
Proof.
	intros A B C D.
	intros TarskiPar_AB_CD.

	destruct TarskiPar_AB_CD as (neq_A_B & neq_C_D & n_Meet_A_B_C_D & SameSide_C_D_AB).

	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_neq_symmetric _ _ neq_C_D) as neq_D_C.

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_C_D_AB) as (SameSide_D_C_AB & _ & _).
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_C_D_AB) as (_ & SameSide_C_D_BA & _).
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_C_D_BA) as (SameSide_D_C_BA & _ & _).

	assert (~ Meet A B D C) as n_Meet_A_B_D_C.
	{
		intro Meet_A_B_D_C.

		destruct Meet_A_B_D_C as (T & _ & _ & Col_A_B_T & Col_D_C_T).

		pose proof (by_prop_Col_order _ _ _ Col_D_C_T) as (Col_C_D_T & _ & _ & _ & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_T Col_C_D_T) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	pose proof (by_def_TarskiPar _ _ _ _ neq_A_B neq_D_C n_Meet_A_B_D_C SameSide_D_C_AB) as TarskiPar_AB_DC.

	assert (~ Meet B A C D) as n_Meet_B_A_C_D.
	{
		intro Meet_B_A_C_D.

		destruct Meet_B_A_C_D as (T & _ & _ & Col_B_A_T & Col_C_D_T).

		pose proof (by_prop_Col_order _ _ _ Col_B_A_T) as (Col_A_B_T & _ & _ & _ & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_T Col_C_D_T) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	pose proof (by_def_TarskiPar _ _ _ _ neq_B_A neq_C_D n_Meet_B_A_C_D SameSide_C_D_BA) as TarskiPar_BA_CD.

	assert (~ Meet B A D C) as n_Meet_B_A_D_C.
	{
		intro Meet_B_A_D_C.

		destruct Meet_B_A_D_C as (T & _ & _ & Col_B_A_T & Col_D_C_T).

		pose proof (by_prop_Col_order _ _ _ Col_B_A_T) as (Col_A_B_T & _ & _ & _ & _).
		pose proof (by_prop_Col_order _ _ _ Col_D_C_T) as (Col_C_D_T & _ & _ & _ & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_T Col_C_D_T) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	pose proof (by_def_TarskiPar _ _ _ _ neq_B_A neq_D_C n_Meet_B_A_D_C SameSide_D_C_BA) as TarskiPar_BA_DC.

	split.
	exact TarskiPar_BA_CD.
	split.
	exact TarskiPar_AB_DC.
	exact TarskiPar_BA_DC.
Qed.

End Euclid.
