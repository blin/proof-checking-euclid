Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_CongA_reflexive :
	forall A B C,
	nCol A B C ->
	CongA A B C A B C.
Proof.
	intros A B C.
	intros nCol_A_B_C.

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_B_C) as CongA_ABC_CBA.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_ABC_CBA) as nCol_C_B_A.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_C_B_A) as CongA_CBA_ABC.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_CBA CongA_CBA_ABC) as CongA_ABC_ABC.
	exact CongA_ABC_ABC.
Qed.

End Euclid.
