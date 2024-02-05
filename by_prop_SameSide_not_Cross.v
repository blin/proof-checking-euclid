Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_SameSide_not_OppositeSide.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_SameSide_not_Cross :
	forall A B C D,
	SameSide A B C D ->
	~ Cross A B C D.
Proof.
	intros A B C D.
	intros SameSide_A_B_CD.

	pose proof (by_prop_SameSide_not_OppositeSide _ _ _ _ SameSide_A_B_CD) as n_OppositeSide_A_CD_B.

	destruct SameSide_A_B_CD as (_ & _ & _ & _ & _ & _ & _ & nCol_C_D_A & nCol_C_D_B).

	assert (~ Cross A B C D) as n_Cross_AB_CD.
	{
		intros Cross_AB_CD.

		destruct Cross_AB_CD as (M & BetS_A_M_B & BetS_C_M_D).

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_M_D) as Col_C_M_D.
		pose proof (by_prop_Col_order _ _ _ Col_C_M_D) as (Col_M_C_D & Col_M_D_C & Col_D_C_M & Col_C_D_M & Col_D_M_C).

		pose proof (by_def_OppositeSide _ _ _ _ _ BetS_A_M_B Col_C_D_M nCol_C_D_A) as OppositeSide_A_CD_B.

		contradict OppositeSide_A_CD_B.
		exact n_OppositeSide_A_CD_B.
	}

	exact n_Cross_AB_CD.
Qed.

End Euclid.
