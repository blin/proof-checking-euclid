Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NChelper.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_oppositesidesymmetric.
Require Import ProofCheckingEuclid.lemma_s_ss.
Require Import ProofCheckingEuclid.lemma_s_supp.
Require Import ProofCheckingEuclid.lemma_supplements_conga.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_07.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_14 :
	forall A B C D E,
	SumTwoRT A B C D B E ->
	OnRay B C D ->
	OppositeSide E D B A ->
	Supp A B C D E /\ BetS A B E.
Proof.
	intros A B C D E.
	intros SumTwoRT_ABC_DBE.
	intros OnRay_BC_D.
	intros OppositeSide_E_DB_A.

	pose proof (cn_congruencereflexive B D) as Cong_BD_BD.

	assert (eq B B) as eq_B_B by (reflexivity).
	assert (Col A B B) as Col_A_B_B by (unfold Col; one_of_disjunct eq_B_B).
	assert (Col D B B) as Col_D_B_B by (unfold Col; one_of_disjunct eq_B_B).
	assert (Col C B B) as Col_C_B_B by (unfold Col; one_of_disjunct eq_B_B).

	destruct SumTwoRT_ABC_DBE as (a & b & e & c & d & Supp_abc_dbe & CongA_ABC_abc & CongA_DBE_dbe).

	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_ABC_abc) as CongA_abc_ABC.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_DBE_dbe) as CongA_dbe_DBE.

	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_abc_ABC) as nCol_A_B_C.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_dbe_DBE) as nCol_D_B_E.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & _ & _ & _ & _ & _).
	pose proof (lemma_NCdistinct _ _ _ nCol_D_B_E) as (neq_D_B & neq_B_E & _ & _ & _ & _).

	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_BC_D) as Col_B_C_D.
	pose proof (lemma_collinearorder _ _ _ Col_B_C_D) as (Col_C_B_D & _ & _ & _ & _).

	pose proof (lemma_oppositesidesymmetric _ _ _ _ OppositeSide_E_DB_A) as OppositeSide_A_DB_E.

	pose proof (lemma_extension _ _ _ _ neq_A_B neq_B_E) as (T & BetS_A_B_T & Cong_BT_BE).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_T) as BetS_T_B_A.

	assert (Col A B T) as Col_A_B_T by (unfold Col; one_of_disjunct BetS_A_B_T).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_T) as (neq_B_T & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_B_T) as neq_T_B.
	pose proof (lemma_NChelper _ _ _ _ _ nCol_A_B_C Col_A_B_T Col_A_B_B neq_T_B) as nCol_T_B_C.
	pose proof (lemma_NCorder _ _ _ nCol_T_B_C) as (_ & _ & _ & _ & nCol_C_B_T).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_C_B_T Col_C_B_D Col_C_B_B neq_D_B) as nCol_D_B_T.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_BT_BE) as (Cong_TB_EB & _ & _).

	pose proof (lemma_s_supp _ _ _ _ _ OnRay_BC_D BetS_A_B_T) as Supp_ABC_DBT.
	pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_abc_ABC Supp_abc_dbe Supp_ABC_DBT) as CongA_dbe_DBT.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_DBE_dbe CongA_dbe_DBT) as CongA_DBE_DBT.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_DBE_DBT) as CongA_DBT_DBE.

	pose proof (proposition_04 _ _ _ _ _ _ Cong_BD_BD Cong_BT_BE CongA_DBT_DBE) as (Cong_DT_DE & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_DT_DE) as (Cong_TD_ED & _ & _).

	destruct OppositeSide_A_DB_E as (m & BetS_A_m_E & Col_D_B_m & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_m_E) as BetS_E_m_A.

	pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_D_B_B Col_D_B_m BetS_T_B_A BetS_E_m_A nCol_D_B_T nCol_D_B_E) as SameSide_T_E_DB.
	pose proof (proposition_07 _ _ _ _ neq_D_B Cong_TD_ED Cong_TB_EB SameSide_T_E_DB) as eq_T_E.
	assert (BetS A B E) as BetS_A_B_E by (rewrite <- eq_T_E; exact BetS_A_B_T).

	pose proof (lemma_s_supp _ _ _ _ _ OnRay_BC_D BetS_A_B_E) as Supp_ABC_DBE.

	split.
	exact Supp_ABC_DBE.
	exact BetS_A_B_E.
Qed.

End Euclid.
