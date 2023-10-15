Require Import ProofCheckingEuclid.by_def_SumTwoRT.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_SumTwoRT_congruence :
	forall A B C D E F P Q R,
	SumTwoRT A B C D E F ->
	CongA A B C P Q R ->
	SumTwoRT P Q R D E F.
Proof.
	intros A B C D E F P Q R.
	intros SumTwoRT_ABC_DEF.
	intros CongA_ABC_PQR.

	destruct SumTwoRT_ABC_DEF as (a & b & c & d & e & Supp_abc_dbe & CongA_ABC_abc & CongA_DEF_dbe).

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ABC_PQR) as CongA_PQR_ABC.

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_PQR_ABC CongA_ABC_abc) as CongA_PQR_abc.
	pose proof (by_def_SumTwoRT _ _ _ _ _ _ _ _ _ _ _ Supp_abc_dbe CongA_PQR_abc CongA_DEF_dbe) as SumTwoRT_PQR_DEF.

	exact SumTwoRT_PQR_DEF.
Qed.

End Euclid.

