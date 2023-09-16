Require Import ProofCheckingEuclid.by_prop_SameSide_not_Cross .
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_crisscross.
Require Import ProofCheckingEuclid.proposition_33.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_33B :
	forall A B C D,
	Par A B C D ->
	Cong A B C D ->
	SameSide A C B D ->
	Par A C B D /\ Cong A C B D.
Proof.
	intros A B C D.
	intros Par_AB_CD.
	intros Cong_AB_CD.
	intros SameSide_A_C_BD.

	epose proof (by_prop_SameSide_not_Cross _ _ _ _ SameSide_A_C_BD) as n_Cross_A_C_B_D.
	pose proof (lemma_crisscross _ _ _ _ Par_AB_CD n_Cross_A_C_B_D) as Cross_A_D_C_B.

	destruct Cross_A_D_C_B as (m & BetS_A_m_D & BetS_C_m_B).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_m_B) as BetS_B_m_C.

	pose proof (proposition_33 _ _ _ _ _ Par_AB_CD Cong_AB_CD BetS_A_m_D BetS_B_m_C) as (Par_AC_BD & Cong_AC_BD).

	split.
	exact Par_AC_BD.
	exact Cong_AC_BD.
Qed.

End Euclid.
