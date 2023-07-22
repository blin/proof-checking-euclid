Require Import ProofCheckingEuclid.by_def_InCirc_center.
Require Import ProofCheckingEuclid.by_def_InCirc_within_radius.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_differenceofparts.
Require Import ProofCheckingEuclid.proposition_01.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_02 :
	forall A B C,
	neq A B ->
	neq B C ->
	exists X, Cong A X B C.
Proof.
	intros A B C.
	intros neq_A_B.
	intros neq_B_C.

	pose proof (proposition_01 _ _ neq_A_B) as (D & equilateral_ABD & Triangle_ABD).

	destruct equilateral_ABD as (_ & Cong_BD_DA).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BD_DA) as Cong_DA_BD.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BD_DA) as (_ & Cong_DB_DA & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_DA_BD) as (_ & _ & Cong_DA_DB).

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_ABD) as nCol_A_B_D.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_D) as (_ & neq_B_D & neq_A_D & neq_B_A & neq_D_B & neq_D_A).

	pose proof (postulate_Euclid3 _ _ neq_B_C) as (K & CI_K_B_BC).

	pose proof (by_def_InCirc_center _ _ _ _ CI_K_B_BC) as InCirc_B_K.

	pose proof (postulate_line_circle _ _ _ _ _ _ CI_K_B_BC InCirc_B_K neq_D_B) as (_ & G & _ & BetS_D_B_G & _ & OnCirc_D_K & _).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_D_B_G) as (_ & _ & neq_D_G).

	pose proof (axiom_circle_center_radius _ _ _ _ _ CI_K_B_BC OnCirc_D_K) as Cong_BG_BC.

	pose proof (postulate_Euclid3 _ _ neq_D_G) as (J & CI_J_D_DG).

	pose proof (cn_congruencereflexive D G) as Cong_DG_DG.

	pose proof (by_def_InCirc_within_radius _ _ _ _ _ _ _ CI_J_D_DG BetS_D_B_G Cong_DG_DG Cong_DA_DB) as InCirc_A_J.

	pose proof (postulate_line_circle _ _ _ _ _ _ CI_J_D_DG InCirc_A_J neq_D_A) as (_ & L & _ & BetS_D_A_L & _ & OnCirc_L_J & _).

	pose proof (axiom_circle_center_radius _ _ _ _ _ CI_J_D_DG OnCirc_L_J) as Cong_DL_DG.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_DL_DG) as Cong_DG_DL.

	pose proof (lemma_differenceofparts _ _ _ _ _ _ Cong_DB_DA Cong_DG_DL BetS_D_B_G BetS_D_A_L) as Cong_BG_AL.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BG_AL) as Cong_AL_BG.

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AL_BG Cong_BG_BC) as Cong_AL_BC.

	exists L.
	exact Cong_AL_BC.
Qed.

End Euclid.
