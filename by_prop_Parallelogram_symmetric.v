Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_Parallelogram_symmetric :
	forall A B C D,
	Parallelogram A B C D ->
	Parallelogram C D A B.
Proof.
	intros A B C D.
	intros Parallelogram_A_B_C_D.


	destruct Parallelogram_A_B_C_D as (Par_AB_CD & Par_AD_BC).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AB_CD) as Par_CD_AB.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AD_BC) as Par_BC_AD.
	pose proof (by_prop_Par_flip _ _ _ _ Par_BC_AD) as (_ & _ & Par_CB_DA).
	pose proof (by_def_Parallelogram _ _ _ _ Par_CD_AB Par_CB_DA) as Parallelogram_C_D_A_B.

	exact Parallelogram_C_D_A_B.
Qed.

End Euclid.

