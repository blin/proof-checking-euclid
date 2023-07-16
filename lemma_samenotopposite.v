Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.


Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_samenotopposite :
	forall A B C D,
	SameSide A B C D ->
	~ OppositeSide A C D B.
Proof.
	intros A B C D.
	intros SameSide_A_B_CD.

	pose proof (lemma_samesidesymmetric _ _ _ _ SameSide_A_B_CD) as (SameSide_B_A_CD & _ & _).

	assert (~ OppositeSide A C D B) as n_OppositeSide_A_CD_B.
	{
		intro OppositeSide_A_CD_B.
		pose proof (lemma_planeseparation _ _ _ _ _ SameSide_B_A_CD OppositeSide_A_CD_B) as OppositeSide_B_CD_B.

		destruct OppositeSide_B_CD_B as (M & BetS_B_M_B & _).

		pose proof (axiom_betweennessidentity B M) as n_BetS_B_M_B.

		contradict BetS_B_M_B.
		exact n_BetS_B_M_B.
	}

	exact n_OppositeSide_A_CD_B.
Qed.

End Euclid.
