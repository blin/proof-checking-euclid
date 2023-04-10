Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence_smaller.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_lta.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_10.
Require Import ProofCheckingEuclid.proposition_15.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_16 :
	forall A B C D,
	Triangle A B C ->
	BetS B C D ->
	LtA B A C A C D /\ LtA C B A A C D.
Proof.
	intros A B C D.
	intros Triangle_A_B_C.
	intros BetS_B_C_D.

	pose proof (lemma_betweennotequal _ _ _ BetS_B_C_D) as (_ & _ & neq_B_D).
	pose proof (lemma_inequalitysymmetric B D neq_B_D) as neq_D_B.
	pose proof (lemma_s_col_BetS_A_B_C B C D BetS_B_C_D) as Col_B_C_D.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_C_D) as BetS_D_C_B.
	pose proof (lemma_collinearorder _ _ _ Col_B_C_D) as (Col_C_B_D & Col_C_D_B & Col_D_B_C & Col_B_D_C & Col_D_C_B).

	pose proof (lemma_s_ncol_triangle A B C Triangle_A_B_C) as nCol_A_B_C.
	pose proof (lemma_s_ncol_n_col A B C nCol_A_B_C) as n_Col_A_B_C.

	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_B_A_C) as n_Col_B_A_C.


	pose proof (proposition_10 A C neq_A_C) as (E & BetS_A_E_C & Cong_E_A_E_C).

	assert (~ eq B E) as neq_B_E.
	{
		intro eq_B_E.

		assert (BetS A B C) as BetS_A_B_C by (rewrite eq_B_E; exact BetS_A_E_C).

		pose proof (lemma_s_col_BetS_A_B_C A B C BetS_A_B_C) as Col_A_B_C.

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (lemma_inequalitysymmetric B E neq_B_E) as neq_E_B.
	pose proof (lemma_extension B E E B neq_B_E neq_E_B) as (F & BetS_B_E_F & Cong_E_F_E_B).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_E_C) as (neq_E_C & _ & _).

	pose proof (lemma_extension A C E C neq_A_C neq_E_C) as (G & BetS_A_C_G & Cong_C_G_E_C).

	pose proof (lemma_s_col_BetS_A_B_C A E C BetS_A_E_C) as Col_A_E_C.
	pose proof (lemma_collinearorder _ _ _ Col_A_E_C) as (Col_E_A_C & Col_E_C_A & Col_C_A_E & Col_A_C_E & Col_C_E_A).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_E_C) as (_ & neq_A_E & _).
	pose proof (lemma_inequalitysymmetric A E neq_A_E) as neq_E_A.

	assert (~ Col B E A) as n_Col_B_E_A.
	{
		intro Col_B_E_A.

		pose proof (lemma_collinearorder _ _ _ Col_B_E_A) as (_ & Col_E_A_B & _ & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD E A B C Col_E_A_B Col_E_A_C neq_E_A) as Col_A_B_C.

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_B_E_A) as nCol_B_E_A.
	pose proof (lemma_NCorder _ _ _ nCol_B_E_A) as (nCol_E_B_A & nCol_E_A_B & nCol_A_B_E & nCol_B_A_E & nCol_A_E_B).

	pose proof (proposition_15 B F A C E BetS_B_E_F BetS_A_E_C nCol_B_E_A) as (CongA_B_E_A_C_E_F & _).


	pose proof (lemma_ABCequalsCBA A E B nCol_A_E_B) as CongA_A_E_B_B_E_A.
	pose proof (lemma_equalanglestransitive A E B B E A C E F CongA_A_E_B_B_E_A CongA_B_E_A_C_E_F) as CongA_A_E_B_C_E_F.

	pose proof (lemma_doublereverse E F E B Cong_E_F_E_B) as (Cong_B_E_F_E & _).
	pose proof (lemma_congruenceflip B E F E Cong_B_E_F_E) as (Cong_E_B_E_F & _ & _).

	pose proof (proposition_04 E A B E C F Cong_E_A_E_C Cong_E_B_E_F CongA_A_E_B_C_E_F) as (Cong_A_B_C_F & CongA_E_A_B_E_C_F & CongA_E_B_A_E_F_C).

	pose proof (lemma_s_onray_assert_bets_AEB A C E BetS_A_E_C neq_A_C) as OnRay_A_C_E.
	assert (eq B B) as eq_B_B by (reflexivity).

	pose proof (lemma_s_onray_assert_ABB A B neq_A_B) as OnRay_A_B_B.

	pose proof (lemma_equalanglesreflexive B A C nCol_B_A_C) as CongA_B_A_C_B_A_C.
	pose proof (lemma_equalangleshelper B A C B A C B E CongA_B_A_C_B_A_C OnRay_A_B_B OnRay_A_C_E) as CongA_B_A_C_B_A_E.
	pose proof (lemma_ABCequalsCBA B A E nCol_B_A_E) as CongA_B_A_E_E_A_B.
	pose proof (lemma_equalanglestransitive B A C B A E E A B CongA_B_A_C_B_A_E CongA_B_A_E_E_A_B) as CongA_B_A_C_E_A_B.
	pose proof (lemma_equalanglestransitive B A C E A B E C F CongA_B_A_C_E_A_B CongA_E_A_B_E_C_F) as CongA_B_A_C_E_C_F.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_C) as BetS_C_E_A.

	pose proof (lemma_betweennotequal _ _ _ BetS_C_E_A) as (_ & neq_C_E & _).

	pose proof (lemma_s_onray_assert_bets_ABE C E A BetS_C_E_A neq_C_E) as OnRay_C_E_A.
	assert (eq F F) as eq_F_F by (reflexivity).

	pose proof (lemma_betweennotequal _ _ _ BetS_B_E_F) as (neq_E_F & _ & _).
	pose proof (lemma_inequalitysymmetric E F neq_E_F) as neq_F_E.
	pose proof (lemma_s_col_BetS_A_B_C B E F BetS_B_E_F) as Col_B_E_F.
	pose proof (lemma_collinearorder _ _ _ Col_B_E_F) as (Col_E_B_F & Col_E_F_B & Col_F_B_E & Col_B_F_E & Col_F_E_B).
	pose proof (lemma_betweennotequal _ _ _ BetS_B_E_F) as (_ & _ & neq_B_F).
	pose proof (lemma_inequalitysymmetric B F neq_B_F) as neq_F_B.

	assert (~ Col E C F) as n_Col_E_C_F.
	{
		intro Col_E_C_F.

		pose proof (lemma_collinearorder _ _ _ Col_E_C_F) as (_ & _ & Col_F_E_C & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD F E B C Col_F_E_B Col_F_E_C neq_F_E) as Col_E_B_C.
		pose proof (lemma_collinearorder _ _ _ Col_E_B_C) as (_ & _ & _ & Col_E_C_B & _).
		pose proof (lemma_collinear_ABC_ABD_BCD E C B A Col_E_C_B Col_E_C_A neq_E_C) as Col_C_B_A.
		pose proof (lemma_collinearorder _ _ _ Col_C_B_A) as (_ & _ & _ & _ & Col_A_B_C).

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_E_C_F) as nCol_E_C_F.
	pose proof (lemma_NCdistinct _ _ _ nCol_E_C_F) as (_ & neq_C_F & _ & _ & neq_F_C & _).
	pose proof (lemma_NCorder _ _ _ nCol_E_C_F) as (nCol_C_E_F & nCol_C_F_E & nCol_F_E_C & nCol_E_F_C & nCol_F_C_E).

	pose proof (lemma_s_onray_assert_ABB C F neq_C_F) as OnRay_C_F_F.
	pose proof (lemma_equalanglesreflexive E C F nCol_E_C_F) as CongA_E_C_F_E_C_F.
	pose proof (lemma_equalangleshelper E C F E C F A F CongA_E_C_F_E_C_F OnRay_C_E_A OnRay_C_F_F) as CongA_E_C_F_A_C_F.
	pose proof (lemma_equalanglestransitive B A C E C F A C F CongA_B_A_C_E_C_F CongA_E_C_F_A_C_F) as CongA_B_A_C_A_C_F.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_E_F) as BetS_F_E_B.

	assert (~ Col D B F) as n_Col_D_B_F.
	{
		intro Col_D_B_F.

		pose proof (lemma_collinearorder _ _ _ Col_D_B_F) as (_ & _ & _ & _ & Col_F_B_D).
		pose proof (lemma_collinear_ABC_ABD_BCD F B D E Col_F_B_D Col_F_B_E neq_F_B) as Col_B_D_E.
		pose proof (lemma_collinearorder _ _ _ Col_B_D_E) as (Col_D_B_E & _ & _ & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD D B E C Col_D_B_E Col_D_B_C neq_D_B) as Col_B_E_C.
		pose proof (lemma_collinearorder _ _ _ Col_B_E_C) as (_ & Col_E_C_B & _ & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD E C B A Col_E_C_B Col_E_C_A neq_E_C) as Col_C_B_A.
		pose proof (lemma_collinearorder _ _ _ Col_C_B_A) as (_ & _ & _ & _ & Col_A_B_C).

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_D_B_F) as nCol_D_B_F.
	pose proof (lemma_NCdistinct _ _ _ nCol_D_B_F) as (_ & _ & neq_D_F & _ & _ & neq_F_D).
	pose proof (lemma_NCorder _ _ _ nCol_D_B_F) as (nCol_B_D_F & nCol_B_F_D & nCol_F_D_B & nCol_D_F_B & nCol_F_B_D).

	epose proof (postulate_Pasch_inner D F B C E BetS_D_C_B BetS_F_E_B nCol_D_B_F) as (H & BetS_D_H_E & BetS_F_H_C).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_H_C) as BetS_C_H_F.
	pose proof (lemma_s_onray_assert_bets_AEB C F H BetS_C_H_F neq_C_F) as OnRay_C_F_H.
	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB C A neq_C_A) as OnRay_C_A_A.
	pose proof (lemma_equalangleshelper B A C A C F A H CongA_B_A_C_A_C_F OnRay_C_A_A OnRay_C_F_H) as CongA_B_A_C_A_C_H.
	(*pose proof (lemma_equalangleshelper B A C X C Z A F CongA_B_A_C_X_C_Z OnRay_C_X_A OnRay_C_Z_F) as CongA_B_A_C_A_C_F.*)
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_H_E) as BetS_E_H_D.
	pose proof (lemma_onray_ABC_ACB C E A OnRay_C_E_A) as OnRay_C_A_E.
	assert (eq D D) as eq_D_D by (reflexivity).

	pose proof (lemma_betweennotequal _ _ _ BetS_D_C_B) as (_ & neq_D_C & _).

	pose proof (lemma_inequalitysymmetric D C neq_D_C) as neq_C_D.
	pose proof (lemma_s_onray_assert_ABB C D neq_C_D) as OnRay_C_D_D.
	pose proof (lemma_s_lta B A C A C D E _ D BetS_E_H_D OnRay_C_A_E OnRay_C_D_D CongA_B_A_C_A_C_H) as LtA_B_A_C_A_C_D.

	pose proof (proposition_10 B C neq_B_C) as (e & BetS_B_e_C & Cong_e_B_e_C).

	pose proof (lemma_betweennotequal _ _ _ BetS_B_e_C) as (_ & neq_B_e & _).
		pose proof (lemma_inequalitysymmetric B e neq_B_e) as neq_e_B.
	pose proof (lemma_s_col_BetS_A_B_C B e C BetS_B_e_C) as Col_B_e_C.
	pose proof (lemma_collinearorder _ _ _ Col_B_e_C) as (Col_e_B_C & Col_e_C_B & Col_C_B_e & Col_B_C_e & Col_C_e_B).

	assert (~ eq A e) as neq_A_e.
	{
		intro eq_A_e.

		assert (BetS B A C) as BetS_B_A_C by (rewrite eq_A_e; exact BetS_B_e_C).

		pose proof (lemma_s_col_BetS_A_B_C B A C BetS_B_A_C) as Col_B_A_C.


		contradict Col_B_A_C.
		exact n_Col_B_A_C.
	}
	pose proof (lemma_inequalitysymmetric A e neq_A_e) as neq_e_A.
	pose proof (lemma_extension A e e A neq_A_e neq_e_A) as (f & BetS_A_e_f & Cong_e_f_e_A).

	assert (~ Col A e B) as n_Col_A_e_B.
	{
		intro Col_A_e_B.

		pose proof (lemma_collinearorder _ _ _ Col_A_e_B) as (_ & Col_e_B_A & _ & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD e B A C Col_e_B_A Col_e_B_C neq_e_B) as Col_B_A_C.

		contradict Col_B_A_C.
		exact n_Col_B_A_C.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_e_B) as nCol_A_e_B.
	pose proof (lemma_NCorder _ _ _ nCol_A_e_B) as (nCol_e_A_B & nCol_e_B_A & nCol_B_A_e & nCol_A_B_e & nCol_B_e_A).

	pose proof (proposition_15 A f B C e BetS_A_e_f BetS_B_e_C nCol_A_e_B) as (CongA_A_e_B_C_e_f & _).

	pose proof (lemma_ABCequalsCBA B e A nCol_B_e_A) as CongA_B_e_A_A_e_B.
	pose proof (lemma_equalanglestransitive B e A A e B C e f CongA_B_e_A_A_e_B CongA_A_e_B_C_e_f) as CongA_B_e_A_C_e_f.

	pose proof (lemma_doublereverse e f e A Cong_e_f_e_A) as (Cong_A_e_f_e & _).

	pose proof (lemma_congruenceflip A e f e Cong_A_e_f_e) as (Cong_e_A_e_f & _ & _).

	pose proof (proposition_04 e B A e C f Cong_e_B_e_C Cong_e_A_e_f CongA_B_e_A_C_e_f) as (Cong_B_A_C_f & CongA_e_B_A_e_C_f & CongA_e_A_B_e_f_C).

	pose proof (lemma_s_onray_assert_bets_AEB B C e BetS_B_e_C neq_B_C) as OnRay_B_C_e.
	pose proof (lemma_s_onray_assert_ABB B A neq_B_A) as OnRay_B_A_A.

	pose proof (lemma_equalanglesreflexive A B C nCol_A_B_C) as CongA_A_B_C_A_B_C.
	pose proof (lemma_equalangleshelper A B C A B C A e CongA_A_B_C_A_B_C OnRay_B_A_A OnRay_B_C_e) as CongA_A_B_C_A_B_e.
	pose proof (lemma_ABCequalsCBA A B e nCol_A_B_e) as CongA_A_B_e_e_B_A.
	pose proof (lemma_equalanglestransitive A B C A B e e B A CongA_A_B_C_A_B_e CongA_A_B_e_e_B_A) as CongA_A_B_C_e_B_A.
	pose proof (lemma_equalanglestransitive A B C e B A e C f CongA_A_B_C_e_B_A CongA_e_B_A_e_C_f) as CongA_A_B_C_e_C_f.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_e_C) as BetS_C_e_B.

	pose proof (lemma_betweennotequal _ _ _ BetS_C_e_B) as (_ & neq_C_e & _).

	pose proof (lemma_s_onray_assert_bets_ABE C e B BetS_C_e_B neq_C_e) as OnRay_C_e_B.
	assert (eq f f) as eq_f_f by (reflexivity).
	epose proof (lemma_equalanglesNC _ _ _ e C f CongA_A_B_C_e_C_f) as nCol_e_C_f.
	pose proof (lemma_NCdistinct _ _ _ nCol_e_C_f) as (neq_e_C & neq_C_f & neq_e_f & _ & neq_f_C & neq_f_e).
	pose proof (lemma_NCorder _ _ _ nCol_e_C_f) as (nCol_C_e_f & nCol_C_f_e & nCol_f_e_C & nCol_e_f_C & nCol_f_C_e).

	pose proof (lemma_s_onray_assert_ABB C f neq_C_f) as OnRay_C_f_f.

	pose proof (lemma_equalanglesreflexive e C f nCol_e_C_f) as CongA_e_C_f_e_C_f.
	pose proof (lemma_equalangleshelper e C f e C f B f CongA_e_C_f_e_C_f OnRay_C_e_B OnRay_C_f_f) as CongA_e_C_f_B_C_f.
	pose proof (lemma_equalanglestransitive A B C e C f B C f CongA_A_B_C_e_C_f CongA_e_C_f_B_C_f) as CongA_A_B_C_B_C_f.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_G) as BetS_G_C_A.

	pose proof (lemma_betweennotequal _ _ _ BetS_G_C_A) as (_ & neq_G_C & _).
	pose proof (lemma_inequalitysymmetric G C neq_G_C) as neq_C_G.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_e_f) as BetS_f_e_A.

	pose proof (lemma_s_col_BetS_A_B_C A C G BetS_A_C_G) as Col_A_C_G.
	pose proof (lemma_collinearorder _ _ _ Col_A_C_G) as (Col_C_A_G & Col_C_G_A & Col_G_A_C & Col_A_G_C & Col_G_C_A).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_C_G) as (_ & _ & neq_A_G).
	pose proof (lemma_inequalitysymmetric A G neq_A_G) as neq_G_A.

	assert (~ Col G A f) as n_Col_G_A_f.
	{
		intro Col_G_A_f.
		pose proof (lemma_collinearorder _ _ _ Col_G_A_f) as (_ & _ & _ & _ & Col_f_A_G).


		pose proof (lemma_s_col_BetS_A_B_C A e f BetS_A_e_f) as Col_A_e_f.

		pose proof (lemma_collinearorder _ _ _ Col_A_e_f) as (_ & _ & Col_f_A_e & _ & _).

		pose proof (lemma_betweennotequal _ _ _ BetS_A_e_f) as (_ & _ & neq_A_f).

		pose proof (lemma_inequalitysymmetric A f neq_A_f) as neq_f_A.
		pose proof (lemma_collinear_ABC_ABD_BCD f A G e Col_f_A_G Col_f_A_e neq_f_A) as Col_A_G_e.

		pose proof (lemma_collinearorder _ _ _ Col_A_G_e) as (Col_G_A_e & _ & _ & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD G A e C Col_G_A_e Col_G_A_C neq_G_A) as Col_A_e_C.

		pose proof (lemma_collinearorder _ _ _ Col_A_e_C) as (_ & Col_e_C_A & _ & _ & _).


		pose proof (lemma_collinear_ABC_ABD_BCD e C A B Col_e_C_A Col_e_C_B neq_e_C) as Col_C_A_B.

		pose proof (lemma_collinearorder _ _ _ Col_C_A_B) as (_ & Col_A_B_C & _ & _ & _).

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_G_A_f) as nCol_G_A_f.
	pose proof (lemma_NCdistinct _ _ _ nCol_G_A_f) as (_ & neq_A_f & neq_G_f & _ & neq_f_A & neq_f_G).
	pose proof (lemma_NCorder _ _ _ nCol_G_A_f) as (nCol_A_G_f & nCol_A_f_G & nCol_f_G_A & nCol_G_f_A & nCol_f_A_G).

	epose proof (postulate_Pasch_inner G f A C e BetS_G_C_A BetS_f_e_A nCol_G_A_f) as (h & BetS_G_h_e & BetS_f_h_C).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_f_h_C) as BetS_C_h_f.

	pose proof (lemma_betweennotequal _ _ _ BetS_f_h_C) as (neq_h_C & _ & _).
	pose proof (lemma_inequalitysymmetric h C neq_h_C) as neq_C_h.
	pose proof (lemma_s_onray_assert_bets_ABE C h f BetS_C_h_f neq_C_h) as OnRay_C_h_f.
	pose proof (lemma_onray_ABC_ACB C h f OnRay_C_h_f) as OnRay_C_f_h.
	pose proof (lemma_s_onray_assert_ABB C B neq_C_B) as OnRay_C_B_B.
	pose proof (lemma_equalangleshelper A B C B C f B h CongA_A_B_C_B_C_f OnRay_C_B_B OnRay_C_f_h) as CongA_A_B_C_B_C_h.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_h_e) as BetS_e_h_G.
	pose proof (lemma_onray_ABC_ACB C e B OnRay_C_e_B) as OnRay_C_B_e.
	assert (eq G G) as eq_G_G by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB C G neq_C_G) as OnRay_C_G_G.
	(*pose proof (lemma_equalanglestransitive A B C X_Y_Z B C h CongA_A_B_C_X_Y_Z CongA_X_Y_Z_B_C_h) as CongA_A_B_C_B_C_h.*)
	epose proof (lemma_s_lta A B C B C G _ _ _ BetS_e_h_G OnRay_C_B_e OnRay_C_G_G CongA_A_B_C_B_C_h) as LtA_A_B_C_B_C_G.

	assert (~ Col G C B) as n_Col_G_C_B.
	{
		intro Col_G_C_B.

		pose proof (lemma_collinear_ABC_ABD_BCD G C B A Col_G_C_B Col_G_C_A neq_G_C) as Col_C_B_A.
		pose proof (lemma_collinearorder _ _ _ Col_C_B_A) as (_ & _ & _ & _ & Col_A_B_C).

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_G_C_B) as nCol_G_C_B.
	pose proof (lemma_NCdistinct _ _ _ nCol_G_C_B) as (_ & _ & neq_G_B & _ & _ & neq_B_G).
	pose proof (lemma_NCorder _ _ _ nCol_G_C_B) as (nCol_C_G_B & nCol_C_B_G & nCol_B_G_C & nCol_G_B_C & nCol_B_C_G).

	pose proof (proposition_15 G A B D C BetS_G_C_A BetS_B_C_D nCol_G_C_B) as (CongA_G_C_B_D_C_A & _).

	assert (~ Col A C D) as n_Col_A_C_D.
	{
		intro Col_A_C_D.

		pose proof (lemma_collinearorder _ _ _ Col_A_C_D) as (_ & _ & _ & _ & Col_D_C_A).
		pose proof (lemma_collinear_ABC_ABD_BCD D C A B Col_D_C_A Col_D_C_B neq_D_C) as Col_C_A_B.
		pose proof (lemma_collinearorder _ _ _ Col_C_A_B) as (_ & Col_A_B_C & _ & _ & _).

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_C_D) as nCol_A_C_D.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_C_D) as (_ & _ & neq_A_D & _ & _ & neq_D_A).
	pose proof (lemma_NCorder _ _ _ nCol_A_C_D) as (nCol_C_A_D & nCol_C_D_A & nCol_D_A_C & nCol_A_D_C & nCol_D_C_A).

	pose proof (lemma_ABCequalsCBA G C B nCol_G_C_B) as CongA_G_C_B_B_C_G.
	pose proof (lemma_angleorderrespectscongruence A B C _ _ _ G C B LtA_A_B_C_B_C_G CongA_G_C_B_B_C_G) as LtA_A_B_C_G_C_B.

	pose proof (lemma_ABCequalsCBA D C A nCol_D_C_A) as CongA_D_C_A_A_C_D.
	pose proof (lemma_equalanglestransitive G C B _ _ _ A C D CongA_G_C_B_D_C_A CongA_D_C_A_A_C_D) as CongA_G_C_B_A_C_D.
	pose proof (lemma_equalanglessymmetric G C B A C D CongA_G_C_B_A_C_D) as CongA_A_C_D_G_C_B.
	pose proof (lemma_angleorderrespectscongruence A B C _ _ _ A C D LtA_A_B_C_G_C_B CongA_A_C_D_G_C_B) as LtA_A_B_C_A_C_D.

	pose proof (lemma_ABCequalsCBA C B A nCol_C_B_A) as CongA_C_B_A_A_B_C.
	pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ A C D C B A LtA_A_B_C_A_C_D CongA_C_B_A_A_B_C) as LtA_C_B_A_A_C_D.

	split.
	exact LtA_B_A_C_A_C_D.
	exact LtA_C_B_A_A_C_D.
Qed.

End Euclid.
