Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
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

	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_ABC_DEF) as nCol_D_E_F.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ABC_DEF) as CongA_DEF_ABC.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_DEF_ABC) as nCol_A_B_C.

	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (_ & _ & _ & _ & nCol_C_B_A).

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_C_B_A) as CongA_CBA_ABC.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_CBA_ABC CongA_ABC_DEF) as CongA_CBA_DEF.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_D_E_F) as CongA_DEF_FED.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_CBA_DEF CongA_DEF_FED) as CongA_CBA_FED.

	exact CongA_CBA_FED.
Qed.

End Euclid.
