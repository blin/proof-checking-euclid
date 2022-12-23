Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_congruenceflip :
	forall A B C D,
	Cong A B C D ->
	Cong B A D C /\ Cong B A C D /\ Cong A B D C.
Proof.
	intros A B C D.
	intros Cong_AB_CD.
	assert (Cong B A A B) as Cong_BA_AB by (apply cn_congruencereverse).
	assert (Cong C D D C) as Cong_CD_DC by (apply cn_congruencereverse).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_BA_AB Cong_AB_CD) as Cong_BA_CD.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_AB_CD Cong_CD_DC) as Cong_AB_DC.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_BA_AB Cong_AB_DC) as Cong_BA_DC.
	split.
	exact Cong_BA_DC.
	split.
	exact Cong_BA_CD.
	exact Cong_AB_DC.
Qed.

End Euclid.


