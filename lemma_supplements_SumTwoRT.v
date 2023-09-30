Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_supplements_conga.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_supplements_SumTwoRT :
	forall A B C D E F J K L P Q R,
	SumTwoRT A B C P Q R ->
	CongA A B C J K L ->
	SumTwoRT J K L D E F ->
	CongA P Q R D E F /\ CongA D E F P Q R.
Proof.
	intros A B C D E F J K L P Q R.
	intros SumTwoRT_ABC_PQR.
	intros CongA_ABC_JKL.
	intros SumTwoRT_JKL_DEF.

	destruct SumTwoRT_ABC_PQR as (a & b & e & c & d & Supp_abc_dbe & CongA_ABC_abc & CongA_PQR_dbe).
	destruct SumTwoRT_JKL_DEF as (j & k & n & l & m & Supp_jkl_mkn & CongA_JKL_jkl & CongA_DEF_mkn).

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ABC_abc) as CongA_abc_ABC.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_DEF_mkn) as CongA_mkn_DEF.

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_abc_ABC CongA_ABC_JKL) as CongA_abc_JKL.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_abc_JKL CongA_JKL_jkl) as CongA_abc_jkl.

	pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_abc_jkl Supp_abc_dbe Supp_jkl_mkn) as CongA_dbe_mkn.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_PQR_dbe CongA_dbe_mkn) as CongA_PQR_mkn.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_PQR_mkn CongA_mkn_DEF) as CongA_PQR_DEF.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_PQR_DEF) as CongA_DEF_PQR.

	split.
	exact CongA_PQR_DEF.
	exact CongA_DEF_PQR.
Qed.

End Euclid.
