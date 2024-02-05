Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_Parallelogram_flip :
	forall A B C D,
	Parallelogram A B C D ->
	Parallelogram B A D C.
Proof.
	intros A B C D.
	intros Parallelogram_A_B_C_D.


	destruct Parallelogram_A_B_C_D as (Par_AB_CD & Par_AD_BC).
	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_CD) as (_ & _ & Par_BA_DC).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AD_BC) as Par_BC_AD.
	pose proof (by_def_Parallelogram _ _ _ _ Par_BA_DC Par_BC_AD) as Parallelogram_B_A_D_C.

	exact Parallelogram_B_A_D_C.
Qed.

End Euclid.

