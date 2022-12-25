Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_extensionunique.
Require Import ProofCheckingEuclid.lemma_localextension.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

(* Originally known as lemma_3_7a *)
Lemma lemma_orderofpoints_ABC_BCD_ACD :
	forall A B C D,
	BetS A B C -> BetS B C D ->
	BetS A C D.
Proof.
	intros A B C D.
	intros BetS_A_B_C.
	intros BetS_B_C_D.
	pose proof (lemma_betweennotequal A B C BetS_A_B_C) as (neq_B_C & neq_A_B & neq_A_C).
	pose proof (lemma_betweennotequal B C D BetS_B_C_D) as (neq_C_D & _ & neq_B_D).
	pose proof (lemma_localextension A C D neq_A_C neq_C_D) as (E & BetS_A_C_E & Cong_CE_CD).
	apply lemma_congruencesymmetric in Cong_CE_CD as Cong_CD_CE.
	pose proof (lemma_orderofpoints_ABC_ACD_BCD A B C E BetS_A_B_C BetS_A_C_E) as BetS_B_C_E.
	pose proof (lemma_extensionunique B C D E BetS_B_C_D BetS_B_C_E Cong_CD_CE) as eq_D_E.
	assert (BetS_A_C_D := BetS_A_C_E).
	replace E with D in BetS_A_C_D.
	exact BetS_A_C_D.
Qed.

End Euclid.

