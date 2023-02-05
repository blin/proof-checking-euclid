Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_differenceofparts.
Require Import ProofCheckingEuclid.lemma_s_incirc_centre.
Require Import ProofCheckingEuclid.lemma_s_incirc_within_radius.
Require Import ProofCheckingEuclid.proposition_01.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_02 :
	forall A B C,
	neq A B -> neq B C ->
	exists X, Cong A X B C.
Proof.
	intros A B C.
	intros neq_A_B neq_B_C.
	pose proof (proposition_01 _ _ neq_A_B) as (D & equilateral_A_B_D & Triangle_A_B_D).
	destruct equilateral_A_B_D as (Cong_AB_BD & Cong_BD_DA).
	apply lemma_congruencesymmetric in Cong_BD_DA as Cong_DA_BD.
	apply lemma_congruenceflip in Cong_DA_BD as (_ & _ & Cong_DA_DB).
	assert (nCol_A_B_D := Triangle_A_B_D).
	unfold Triangle in nCol_A_B_D.

	pose proof (postulate_Euclid3 _ _ neq_B_C) as (J & CI_J_B_BC).
	apply lemma_NCdistinct in nCol_A_B_D as (
		_ & neq_B_D & neq_A_D & neq_B_A & neq_D_B & neq_D_A
	).

	pose proof (lemma_s_incirc_centre _ _ _ _ CI_J_B_BC) as InCirc_B_J.
	pose proof (
		postulate_line_circle _ _ _ _ _ _ CI_J_B_BC InCirc_B_J neq_D_B
	) as (_ & G & _ & BetS_D_B_G & _ & OnCirc_G_J & _).

	pose proof(lemma_betweennotequal _ _ _ BetS_D_B_G) as (neq_B_G & _ & neq_D_G).

	pose proof (postulate_Euclid3 _ _ neq_D_G) as (R & CI_R_D_DG).
	pose proof(axiom_circle_center_radius _ _ _ _ _ CI_J_B_BC OnCirc_G_J) as Cong_BG_BC.

	pose proof(cn_congruencereflexive D G) as Cong_DG_DG.
	pose proof (
		lemma_s_incirc_within_radius _ _ _ _ _ _ B CI_R_D_DG BetS_D_B_G Cong_DG_DG Cong_DA_DB
	) as InCirc_A_R.

	pose proof (
		postulate_line_circle _ _ _ _ _ _ CI_R_D_DG InCirc_A_R neq_D_A
	) as (_ & L & _ & BetS_D_A_L & _ & OnCirc_L_R & _).

	exists L.

	pose proof(axiom_circle_center_radius _ _ _ _ _ CI_R_D_DG OnCirc_L_R) as Cong_DL_DG.

	apply lemma_congruencesymmetric in Cong_DA_DB as Cong_DB_DA.
	apply lemma_congruencesymmetric in Cong_DL_DG as Cong_DG_DL.
	pose proof (
		lemma_differenceofparts _ _ _ _ _ _ Cong_DB_DA Cong_DG_DL BetS_D_B_G BetS_D_A_L
	) as Cong_BG_AL.

	pose proof (cn_congruencetransitive _ _ _ _ _ _ Cong_BG_AL Cong_BG_BC) as Cong_AL_BC.

	exact Cong_AL_BC.
Qed.

End Euclid.
