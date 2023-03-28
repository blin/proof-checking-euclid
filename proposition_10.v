Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_interior5.
Require Import ProofCheckingEuclid.lemma_s_intersecting_triangles_cong_AF_BF.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.proposition_01.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_10 :
	forall A B,
	neq A B ->
	exists X, BetS A X B /\ Cong X A X B.
Proof.
	intros A B.
	intros neq_A_B.

	pose proof (proposition_01 _ _ neq_A_B) as (C & equilateral_A_B_C & Triangle_A_B_C).
	assert (nCol A B C) as nCol_A_B_C by (exact Triangle_A_B_C).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (_ & nCol_B_C_A & _ & nCol_A_C_B & nCol_C_B_A).
	destruct nCol_A_B_C as (_ & neq_A_C & neq_B_C & _ & _ & _).

	pose proof (lemma_inequalitysymmetric _ _ neq_B_C) as neq_C_B.
	pose proof (lemma_extension _ _ _ _ neq_C_B neq_A_B) as (D & BetS_C_B_D & Cong_BD_AB).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_C) as neq_C_A.
	pose proof (lemma_extension _ _ _ _ neq_C_A neq_A_B) as (E & BetS_C_A_E & Cong_AE_AB).

	pose proof (lemma_betweennotequal _ _ _ BetS_C_A_E) as (neq_A_E & _ & neq_C_E).
	pose proof (lemma_betweennotequal _ _ _ BetS_C_B_D) as (_ & _ & neq_C_D).
	pose proof (lemma_betweennotequal _ _ _ BetS_C_B_D) as (neq_B_D & _ & _).
	assert (Col C A E) as Col_C_A_E by (unfold Col; one_of_disjunct BetS_C_A_E).
	assert (Col C B D) as Col_C_B_D by (unfold Col; one_of_disjunct BetS_C_B_D).

	pose proof (lemma_collinearorder _ _ _ Col_C_A_E) as (Col_A_C_E & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_B_D) as (Col_B_C_D & _ & _ & _ & _).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_C_B Col_A_C_E neq_A_E) as nCol_A_E_B.
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_C_A Col_B_C_D neq_B_D) as nCol_B_D_A.
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_C_B_A Col_C_B_D neq_C_D) as nCol_C_D_A.
	pose proof (lemma_NCorder _ _ _ nCol_C_D_A) as (_ & _ & _ & nCol_C_A_D & nCol_A_D_C).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_C_A_D Col_C_A_E neq_C_E) as nCol_C_E_D.
	pose proof (lemma_NCorder _ _ _ nCol_C_E_D) as (_ & _ & nCol_D_C_E & _ & _).
	pose proof (lemma_NCorder _ _ _ nCol_A_E_B) as (_ & _ & nCol_B_A_E & _ & _).
	pose proof (lemma_NCorder _ _ _ nCol_B_D_A) as (_ & _ & nCol_A_B_D & _ & _).


	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_B_D) as BetS_D_B_C.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_A_E) as BetS_E_A_C.

	(* Line BE meets △DCA in side DC and meets extension of side CA. *)
	pose proof (
		postulate_Pasch_inner
		D E C B A
		BetS_D_B_C
		BetS_E_A_C
		nCol_D_C_E
	) as (F & BetS_D_F_A & BetS_E_F_B).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_F_B) as BetS_B_F_E.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_F_A) as BetS_A_F_D.

	(* Line FC meets △ADB in side AD and meets extension of side DB. *)
	pose proof (
		postulate_Pasch_inner
		A C D F B
		BetS_A_F_D
		BetS_C_B_D
		nCol_A_D_C
	) as (M & BetS_A_M_B & BetS_C_M_F).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AE_AB) as Cong_AB_AE.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_BD_AB Cong_AB_AE) as Cong_BD_AE.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BD_AE) as Cong_AE_BD.
	pose proof (cn_congruencereverse A B) as Cong_AB_BA.
	pose proof (cn_congruencereverse B A) as Cong_BA_AB.
	destruct equilateral_A_B_C as (_ & Cong_BC_CA).
	pose proof (lemma_doublereverse _ _ _ _ Cong_BC_CA) as (Cong_AC_CB & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AC_CB) as (_ & Cong_CA_CB & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_BC_CA) as (_ & _ & Cong_BC_AC).
	(* △CAB and △CBA are SSS congruent. *)
	(* △BAE and △ABD are SAS congruent. *)
	(* ∠CAB is supplement to ∠BAE and ∠CBA is supplement to ∠ABD . *)
	(* △BAE ≅ △ABD implies that EB ≅ DA . *)
	pose proof (
		axiom_5_line
		C A E B
		C B D A

		Cong_CA_CB
		Cong_AB_BA
		Cong_BC_AC

		BetS_C_A_E
		BetS_C_B_D

		Cong_BA_AB
		Cong_AE_BD
	) as Cong_EB_DA.

	pose proof (lemma_doublereverse _ _ _ _ Cong_EB_DA) as (Cong_AD_BE & _).
	assert (Triangle A B D) as Triangle_A_B_D by (exact nCol_A_B_D).
	assert (Triangle B A E) as Triangle_B_A_E by (exact nCol_B_A_E).
	pose proof (
		lemma_s_intersecting_triangles_cong_AF_BF
		_ _ _ _ _
		Triangle_A_B_D
		Triangle_B_A_E
		BetS_A_F_D
		BetS_B_F_E
		Cong_AD_BE
		Cong_AE_BD
	) as Cong_AF_BF.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AF_BF) as (Cong_FA_FB & _ & _).

	pose proof (cn_congruencereflexive C M) as Cong_CM_CM.
	pose proof (cn_congruencereflexive M F) as Cong_MF_MF.
	pose proof (
		lemma_interior5
		C M F A
		C M F B
		BetS_C_M_F
		BetS_C_M_F
		Cong_CM_CM
		Cong_MF_MF
		Cong_CA_CB
		Cong_FA_FB
	) as Cong_MA_MB.

	exists M.
	split.
	exact BetS_A_M_B.
	exact Cong_MA_MB.
Qed.

End Euclid.
