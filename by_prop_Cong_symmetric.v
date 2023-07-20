Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma by_prop_Cong_symmetric :
	forall A B C D,
	Cong A B C D ->
	Cong C D A B.
Proof.
	intros A B C D.
	intros Cong_AB_CD.
	assert (Cong A B A B) as Cong_AB_AB by (apply cn_congruencereflexive).
	pose proof (cn_congruencetransitive _ _ _ _ _ _ Cong_AB_CD Cong_AB_AB) as Cong_CD_AB.
	exact Cong_CD_AB.
Qed.

End Euclid.

