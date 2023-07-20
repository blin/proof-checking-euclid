Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_03 :
	forall A B C D E F,
	Lt C D A B ->
	Cong E F A B ->
	exists X, BetS E X F /\ Cong E X C D.
Proof.
	intros A B C D E F.
	intros Lt_CD_AB.
	intros Cong_EF_AB.

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_EF_AB) as Cong_AB_EF.
	pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_CD_AB Cong_AB_EF) as Lt_CD_EF.
	destruct Lt_CD_EF as (G & BetS_E_G_F & Cong_EG_CD).

	exists G.
	split.
	exact BetS_E_G_F.
	exact Cong_EG_CD.
Qed.

End Euclid.
