Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_SameSide_not_Cross.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_crisscross .

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_diagonalsmeet :
	forall A B C D,
	Parallelogram A B C D ->
	exists X, BetS A X C /\ BetS B X D.
Proof.
	intros A B C D.
	intros Parallelogram_A_B_C_D.

	destruct Parallelogram_A_B_C_D as (Par_AB_CD & Par_AD_BC).

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AB_CD) as Par_CD_AB.
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_CD_AB) as TarskiPar_CD_AB.

	destruct TarskiPar_CD_AB as (_ & _ & _ & SameSide_A_B_CD).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_A_B_CD) as (_ & SameSide_A_B_DC & _).
	pose proof (by_prop_SameSide_not_Cross _ _ _ _ SameSide_A_B_DC) as n_Cross_AB_DC.
	pose proof (lemma_crisscross _ _ _ _ Par_AD_BC n_Cross_AB_DC) as Cross_AC_BD.

	destruct Cross_AC_BD as (M & BetS_A_M_C & BetS_B_M_D).

	exists M.
	split.
	exact BetS_A_M_C.
	exact BetS_B_M_D.
Qed.

End Euclid.
