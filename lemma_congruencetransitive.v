Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_congruencetransitive :
	forall A B C D E F,
	Cong A B C D ->
	Cong C D E F ->
	Cong A B E F.
Proof.
	intros A B C D E F.
	intros Cong_AB_CD.
	intros Cong_CD_EF.
	apply lemma_congruencesymmetric in Cong_AB_CD as Cong_CD_AB.
	pose proof (cn_congruencetransitive _ _ _ _ _ _ Cong_CD_AB Cong_CD_EF) as Cong_AB_EF.
	exact Cong_AB_EF.
Qed.

End Euclid.


