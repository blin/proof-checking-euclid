Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_s_incirc_centre.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_localextension.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_outcirc_beyond_perimeter.
Require Import ProofCheckingEuclid.lemma_partnotequalwhole.


Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma proposition_01 :
	forall A B,
	neq A B ->
	exists X, equilateral A B X /\ Triangle A B X .
Proof.
	intros A B.
	intros neq_A_B.
	apply lemma_inequalitysymmetric in neq_A_B as neq_B_A.

	pose proof (postulate_Euclid3 A B neq_A_B) as (J & CI_J_A_AB).
	pose proof (postulate_Euclid3 B A neq_B_A) as (K & CI_K_B_BA).

	pose proof (lemma_localextension _ _ _ neq_B_A neq_A_B) as (D & BetS_B_A_D & Cong_AD_AB).

	assert (Cong B A B A) as Cong_BA_BA by (apply cn_congruencereflexive).

	pose proof (
		lemma_s_outcirc_beyond_perimeter _ _ _ _ _ _ CI_K_B_BA BetS_B_A_D Cong_BA_BA
	) as OutCirc_D_K.

	pose proof (lemma_s_incirc_centre _ _ _ _ CI_K_B_BA) as InCirc_B_K.
	pose proof (lemma_s_incirc_centre _ _ _ _ CI_J_A_AB) as InCirc_A_J.

	assert (Cong A B A B) as Cong_AB_AB by (apply cn_congruencereflexive).

	pose proof (lemma_s_oncirc_radius _ _ _ _ _ CI_J_A_AB Cong_AB_AB) as OnCirc_B_J.
	pose proof (lemma_s_oncirc_radius _ _ _ _ _ CI_J_A_AB Cong_AD_AB) as OnCirc_D_J.

	pose proof (
		postulate_circle_circle
		B A
		A B
		K J
		B D
		B A
		CI_K_B_BA
		InCirc_B_K
		OutCirc_D_K
		CI_J_A_AB
		OnCirc_B_J
		OnCirc_D_J
	) as (C & OnCirc_C_K & OnCirc_C_J).

	exists C.

	pose proof (
		axiom_circle_center_radius
		B B A K C
		CI_K_B_BA
		OnCirc_C_K
	) as Cong_BC_BA.
	apply (lemma_congruencesymmetric) in Cong_BC_BA as Cong_BA_BC.
	apply (lemma_congruenceflip) in Cong_BA_BC as (Cong_AB_CB & Cong_AB_BC & Cong_BC_CB).

	pose proof (
		axiom_circle_center_radius
		A A B J C
		CI_J_A_AB
		OnCirc_C_J
	) as Cong_AC_AB.
	apply (lemma_congruenceflip) in Cong_AC_AB as (Cong_CA_BA & Cong_CA_AB & Cong_AC_BA).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_CA_AB Cong_AB_BC) as Cong_CA_BC.
	apply (lemma_congruencesymmetric) in Cong_CA_BC as Cong_BC_CA.

	split.
	unfold equilateral.
	split.
	exact Cong_AB_BC.
	exact Cong_BC_CA.
	(* equilateral A B X is now proven *)

	apply (lemma_congruencesymmetric) in Cong_CA_AB as Cong_AB_CA.
	apply (lemma_congruenceflip) in Cong_AB_CA as (Cong_BA_AC & Cong_BA_CA & Cong_AB_AC).
	pose proof (axiom_nocollapse A B A C neq_A_B Cong_AB_AC) as neq_A_C.
	pose proof (axiom_nocollapse A B B C neq_A_B Cong_AB_BC) as neq_B_C.

	assert (~ BetS A C B) as nBetS_A_C_B.
	{
		intro BetS_A_C_B.

		pose proof (lemma_partnotequalwhole _ _ _ BetS_A_C_B) as nCong_AC_AB.
		pose proof (cn_congruencereverse C A) as Cong_CA_AC.
		pose proof (cn_congruencereverse A C) as Cong_AC_CA.
		pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_AC_CA Cong_CA_AB) as Cong_AC_AB.

		contradict Cong_AC_AB.
		exact nCong_AC_AB.
	}
	assert (~ BetS A B C) as nBetS_A_B_C.
	{
		intro BetS_A_B_C.

		pose proof (lemma_partnotequalwhole _ _ _ BetS_A_B_C) as nCong_AB_AC.

		contradict Cong_AB_AC.
		exact nCong_AB_AC.
	}
	assert (~ BetS B A C) as nBetS_B_A_C.
	{
		intro BetS_B_A_C.

		pose proof (lemma_partnotequalwhole _ _ _ BetS_B_A_C) as nCong_BA_BC.
		apply lemma_congruencesymmetric in Cong_BC_BA as Cong_BA_BC.

		contradict Cong_BA_BC.
		exact nCong_BA_BC.
	}

	unfold Triangle.
	unfold nCol.
	repeat split.
	exact neq_A_B.
	exact neq_A_C.
	exact neq_B_C.
	exact nBetS_A_B_C.
	exact nBetS_A_C_B.
	exact nBetS_B_A_C.
Qed.

End Euclid.
