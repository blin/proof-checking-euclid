Require Import ProofCheckingEuclid.by_def_SumTwoRT.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Supp_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_SumTwoRT_symmetric :
	forall A B C D E F,
	SumTwoRT A B C D E F ->
	SumTwoRT D E F A B C.
Proof.
	intros A B C D E F.
	intros SumTwoRT_ABC_DEF.

	destruct SumTwoRT_ABC_DEF as (a & b & c & d & e & Supp_abc_dbe & CongA_ABC_abc & CongA_DEF_dbe).

	pose proof (by_prop_Supp_symmetric _ _ _ _ _ Supp_abc_dbe) as Supp_ebd_cba.

	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_ABC_abc) as nCol_a_b_c.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_DEF_dbe) as nCol_d_b_e.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_a_b_c) as CongA_abc_cba.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_d_b_e) as CongA_dbe_ebd.

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_DEF_dbe CongA_dbe_ebd) as CongA_DEF_ebd.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_abc CongA_abc_cba) as CongA_ABC_cba.

	pose proof (by_def_SumTwoRT _ _ _ _ _ _ _ _ _ _ _ Supp_ebd_cba CongA_DEF_ebd CongA_ABC_cba) as SumTwoRT_DEF_ABC.

	exact SumTwoRT_DEF_ABC.
Qed.

End Euclid.
