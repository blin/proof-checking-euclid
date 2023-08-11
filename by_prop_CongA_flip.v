Require Import ProofCheckingEuclid.by_prop_CongA_flip_left.
Require Import ProofCheckingEuclid.by_prop_CongA_flip_right.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_CongA_flip :
	forall A B C D E F,
	CongA A B C D E F ->
	CongA C B A F E D.
Proof.
	intros A B C D E F.
	intros CongA_ABC_DEF.

	pose proof (by_prop_CongA_flip_left _ _ _ _ _ _ CongA_ABC_DEF) as CongA_CBA_DEF.
	pose proof (by_prop_CongA_flip_right _ _ _ _ _ _ CongA_CBA_DEF) as CongA_CBA_FED.

	exact CongA_CBA_FED.
Qed.

End Euclid.
