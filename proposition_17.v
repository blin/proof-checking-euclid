Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NChelper.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence_smaller.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_crossbar.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_neq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.proposition_16.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_17 :
	forall A B C,
	Triangle A B C ->
	exists X Y Z, SumA A B C B C A X Y Z.
Proof.
	intros A B C.
	intros Triangle_A_B_C.

	pose proof (lemma_s_ncol_triangle A B C Triangle_A_B_C) as nCol_A_B_C.
	pose proof (lemma_s_ncol_n_col A B C nCol_A_B_C) as n_Col_A_B_C.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).
	pose proof (lemma_extension B C B C neq_B_C neq_B_C) as (D & BetS_B_C_D & Cong_C_D_B_C).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (lemma_s_col_BetS_A_B_C B C D BetS_B_C_D) as Col_B_C_D.
	assert (eq B B) as eq_B_B by (reflexivity).
	pose proof (lemma_s_col_eq_A_C B C B eq_B_B) as Col_B_C_B.
	pose proof (lemma_betweennotequal _ _ _ BetS_B_C_D) as (_ & _ & neq_B_D).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_B_C_A Col_B_C_B Col_B_C_D neq_B_D) as nCol_B_D_A.
	pose proof (lemma_NCorder _ _ _ nCol_B_D_A) as (nCol_D_B_A & nCol_D_A_B & nCol_A_B_D & nCol_B_A_D & nCol_A_D_B).
	
	pose proof (proposition_16 A B C D Triangle_A_B_C BetS_B_C_D) as (_ & LtA_C_B_A_A_C_D).
	
	pose proof (lemma_ABCequalsCBA A B C nCol_A_B_C) as CongA_A_B_C_C_B_A.
	pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_C_B_A_A_C_D CongA_A_B_C_C_B_A) as LtA_A_B_C_A_C_D.
	destruct LtA_A_B_C_A_C_D as (a & e & d & BetS_a_e_d & OnRay_C_A_a & OnRay_C_D_d & CongA_A_B_C_A_C_e).
	pose proof (lemma_onray_ABC_ACB C A a OnRay_C_A_a) as OnRay_C_a_A.
	pose proof (lemma_onray_ABC_ACB C D d OnRay_C_D_d) as OnRay_C_d_D.
	assert (eq C C) as eq_C_C by (reflexivity).
	pose proof (lemma_s_col_eq_B_C B C C eq_C_C) as Col_B_C_C.
	pose proof (lemma_betweennotequal _ _ _ BetS_B_C_D) as (neq_C_D & _ & _).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_B_C_A Col_B_C_C Col_B_C_D neq_C_D) as nCol_C_D_A.
	pose proof (lemma_s_col_eq_A_C C D C eq_C_C) as Col_C_D_C.
	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_C_D_d) as Col_C_D_d.
	pose proof (lemma_onray_neq_A_B _ _ _ OnRay_C_d_D) as neq_C_d.
	pose proof (lemma_NChelper _ _ _ _ _ nCol_C_D_A Col_C_D_C Col_C_D_d neq_C_d) as nCol_C_d_A.
	pose proof (lemma_NCorder _ _ _ nCol_C_d_A) as (nCol_d_C_A & nCol_d_A_C & nCol_A_C_d & nCol_C_A_d & nCol_A_d_C).
	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_C_A_a) as Col_C_A_a.
	pose proof (lemma_s_col_eq_A_C C A C eq_C_C) as Col_C_A_C.
	pose proof (lemma_onray_neq_A_B _ _ _ OnRay_C_a_A) as neq_C_a.
	pose proof (lemma_NChelper _ _ _ _ _ nCol_C_A_d Col_C_A_C Col_C_A_a neq_C_a) as nCol_C_a_d.
	pose proof (lemma_NCorder _ _ _ nCol_C_a_d) as (nCol_a_C_d & nCol_a_d_C & nCol_d_C_a & nCol_C_d_a & nCol_d_a_C).
	pose proof (lemma_NCorder _ _ _ nCol_C_D_A) as (nCol_D_C_A & nCol_D_A_C & nCol_A_C_D & nCol_C_A_D & nCol_A_D_C).
	pose proof (lemma_s_triangle a C d nCol_a_C_d) as Triangle_a_C_d.
	pose proof (lemma_crossbar _ _ _ _ _ _ Triangle_a_C_d BetS_a_e_d OnRay_C_a_A OnRay_C_d_D) as (E & OnRay_C_e_E & BetS_A_E_D).
	pose proof (lemma_onray_ABC_ACB C e E OnRay_C_e_E) as OnRay_C_E_e.
	pose proof (lemma_s_col_BetS_A_B_C A E D BetS_A_E_D) as Col_A_E_D.
	pose proof (lemma_collinearorder _ _ _ Col_A_E_D) as (Col_E_A_D & Col_E_D_A & Col_D_A_E & Col_A_D_E & Col_D_E_A).
	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (lemma_s_col_eq_B_C D A A eq_A_A) as Col_D_A_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_E_D) as (_ & neq_A_E & _).
	pose proof (lemma_inequalitysymmetric A E neq_A_E) as neq_E_A.
	pose proof (lemma_NChelper _ _ _ _ _ nCol_D_A_C Col_D_A_E Col_D_A_A neq_E_A) as nCol_E_A_C.
	pose proof (lemma_NCorder _ _ _ nCol_E_A_C) as (nCol_A_E_C & nCol_A_C_E & nCol_C_E_A & nCol_E_C_A & nCol_C_A_E).
	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_C_E_e) as Col_C_E_e.
	pose proof (lemma_s_col_eq_A_C C E C eq_C_C) as Col_C_E_C.
	pose proof (lemma_onray_neq_A_B _ _ _ OnRay_C_e_E) as neq_C_e.
	pose proof (lemma_NChelper _ _ _ _ _ nCol_C_E_A Col_C_E_C Col_C_E_e neq_C_e) as nCol_C_e_A.
	pose proof (lemma_NCorder _ _ _ nCol_C_e_A) as (nCol_e_C_A & nCol_e_A_C & nCol_A_C_e & nCol_C_A_e & nCol_A_e_C).
	pose proof (lemma_collinearorder _ _ _ Col_C_A_a) as (Col_A_C_a & Col_A_a_C & Col_a_C_A & Col_C_a_A & Col_a_A_C).
	pose proof (lemma_s_col_eq_B_C A C C eq_C_C) as Col_A_C_C.
	pose proof (lemma_inequalitysymmetric C a neq_C_a) as neq_a_C.
	pose proof (lemma_NChelper _ _ _ _ _ nCol_A_C_e Col_A_C_a Col_A_C_C neq_a_C) as nCol_a_C_e.
	pose proof (lemma_equalanglesreflexive a C e nCol_a_C_e) as CongA_a_C_e_a_C_e.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_a_C_e_a_C_e OnRay_C_a_A OnRay_C_e_E) as CongA_a_C_e_A_C_E.
	assert (eq e e) as eq_e_e by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB C e neq_C_e) as OnRay_C_e_e.
	pose proof (lemma_equalanglesreflexive A C e nCol_A_C_e) as CongA_A_C_e_A_C_e.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_A_C_e_A_C_e OnRay_C_A_a OnRay_C_e_e) as CongA_A_C_e_a_C_e.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_B_C_A_C_e CongA_A_C_e_a_C_e) as CongA_A_B_C_a_C_e.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_B_C_a_C_e CongA_a_C_e_A_C_E) as CongA_A_B_C_A_C_E.
	epose proof (postulate_Pasch_inner A B _ E C BetS_A_E_D BetS_B_C_D nCol_A_D_B) as (F & BetS_A_F_C & BetS_B_F_E).
	pose proof (lemma_s_col_BetS_A_B_C A F C BetS_A_F_C) as Col_A_F_C.
	pose proof (lemma_collinearorder _ _ _ Col_A_F_C) as (Col_F_A_C & Col_F_C_A & Col_C_A_F & Col_A_C_F & Col_C_F_A).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_F_C) as (neq_F_C & _ & _).
	pose proof (lemma_NChelper _ _ _ _ _ nCol_A_C_B Col_A_C_F Col_A_C_C neq_F_C) as nCol_F_C_B.
	pose proof (lemma_NCorder _ _ _ nCol_F_C_B) as (nCol_C_F_B & nCol_C_B_F & nCol_B_F_C & nCol_F_B_C & nCol_B_C_F).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_F_E) as BetS_E_F_B.
	pose proof (lemma_ABCequalsCBA A C E nCol_A_C_E) as CongA_A_C_E_E_C_A.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_B_C_A_C_E CongA_A_C_E_E_C_A) as CongA_A_B_C_E_C_A.
	pose proof (lemma_equalanglesreflexive E C A nCol_E_C_A) as CongA_E_C_A_E_C_A.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_F_C) as BetS_C_F_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_C_F_A) as (_ & neq_C_F & _).
	pose proof (lemma_s_onray_assert_bets_ABE C F A BetS_C_F_A neq_C_F) as OnRay_C_F_A.
	pose proof (lemma_onray_ABC_ACB C F A OnRay_C_F_A) as OnRay_C_A_F.
	assert (eq E E) as eq_E_E by (reflexivity).
	pose proof (lemma_NCdistinct _ _ _ nCol_E_A_C) as (_ & _ & neq_E_C & _ & _ & neq_C_E).
	pose proof (lemma_s_onray_assert_ABB C E neq_C_E) as OnRay_C_E_E.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_E_C_A_E_C_A OnRay_C_E_E OnRay_C_A_F) as CongA_E_C_A_E_C_F.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_B_C_E_C_A CongA_E_C_A_E_C_F) as CongA_A_B_C_E_C_F.
	pose proof (lemma_equalanglesreflexive B C A nCol_B_C_A) as CongA_B_C_A_B_C_A.
	pose proof (lemma_s_onray_assert_ABB C B neq_C_B) as OnRay_C_B_B.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_B_C_A_B_C_A OnRay_C_B_B OnRay_C_A_F) as CongA_B_C_A_B_C_F.
	pose proof (lemma_ABCequalsCBA B C F nCol_B_C_F) as CongA_B_C_F_F_C_B.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_B_C_A_B_C_F CongA_B_C_F_F_C_B) as CongA_B_C_A_F_C_B.
	exists E, C, B.
	unfold SumA.
	exists F.
	split.
	exact CongA_A_B_C_E_C_F.
	split.
	exact CongA_B_C_A_F_C_B.
	exact BetS_E_F_B.
	(*pose proof (SumA) as SumA_A_B_C_B_C_A_E_C_B.*)
Qed.

End Euclid.
