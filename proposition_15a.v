Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.proposition_15.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_15a :
	forall A B C D E : Point,
    BetS A E B ->
    BetS C E D ->
	nCol A E C ->
	CongA A E C D E B.
Proof.
	intros A B C D E.
	intros BetS_A_E_B.
	intros BetS_C_E_D.
	intros nCol_A_E_C.

	pose proof (proposition_15 A B C D E BetS_A_E_B BetS_C_E_D nCol_A_E_C) as (CongA_A_E_C_D_E_B & _).

	exact CongA_A_E_C_D_E_B.
Qed.

End Euclid.
