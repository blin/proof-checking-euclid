Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_Parallelogram_rotate :
	forall A B C D,
	Parallelogram A B C D ->
	Parallelogram B C D A.
Proof.
	intros A B C D.
	intros Parallelogram_A_B_C_D.


	destruct Parallelogram_A_B_C_D as (Par_AB_CD & Par_AD_BC).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AD_BC) as Par_BC_AD.
	pose proof (by_prop_Par_flip _ _ _ _ Par_BC_AD) as (_ & Par_BC_DA & _).
	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_CD) as (Par_BA_CD & _ & _).
	pose proof (by_def_Parallelogram _ _ _ _ Par_BC_DA Par_BA_CD) as Parallelogram_B_C_D_A.

	exact Parallelogram_B_C_D_A.
Qed.

End Euclid.

