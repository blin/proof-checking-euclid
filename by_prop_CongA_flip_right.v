Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_CongA_flip_right :
	forall A B C D E F,
	CongA A B C D E F ->
	CongA A B C F E D.
Proof.
	intros A B C D E F.
	intros CongA_ABC_DEF.

	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_ABC_DEF) as nCol_D_E_F.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_D_E_F) as CongA_DEF_FED.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_DEF CongA_DEF_FED) as CongA_ABC_FED.

	exact CongA_ABC_FED.
Qed.

End Euclid.
