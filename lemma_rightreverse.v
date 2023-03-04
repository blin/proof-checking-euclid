Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_extensionunique.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_rightreverse : 
	forall A B C D,
	RightTriangle A B C ->
	BetS A B D ->
	Cong A B B D ->
	Cong A C D C.
Proof.
	intros A B C D.
	intros RightTriangle_ABC.
	intros BetS_A_B_D.
	intros Cong_AB_BD.

	destruct RightTriangle_ABC as (E & BetS_A_B_E & Cong_AB_EB & Cong_AC_EC & _).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AB_BD) as Cong_BD_AB.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_BD_AB Cong_AB_EB) as Cong_BD_EB.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_BD_EB) as (_ & _ & Cong_BD_BE).
	pose proof (lemma_extensionunique _ _ _ _ BetS_A_B_D BetS_A_B_E Cong_BD_BE) as eq_D_E.
	assert (Cong A C D C) as Cong_AC_DC by (rewrite eq_D_E; exact Cong_AC_EC).

	exact Cong_AC_DC.
Qed.

End Euclid.
