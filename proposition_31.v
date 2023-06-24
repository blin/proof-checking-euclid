Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NChelper.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennesspreserved.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_oppositesidesymmetric.
Require Import ProofCheckingEuclid.lemma_parallelflip.
Require Import ProofCheckingEuclid.lemma_pointreflectionisometry.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_conga.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_midpoint.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.proposition_10.
Require Import ProofCheckingEuclid.proposition_27.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_31 :
	forall A B C D,
	BetS B D C ->
	nCol B C A ->
	exists X Y Z, BetS X A Y /\ CongA Y A D A D B /\ CongA Y A D B D A /\ CongA D A Y B D A /\ CongA X A D A D C /\ CongA X A D C D A /\ CongA D A X C D A /\ Par X Y B C /\ Cong X A D C /\ Cong A Y B D /\ Cong A Z Z D /\ Cong X Z Z C /\ Cong B Z Z Y /\ BetS X Z C /\ BetS B Z Y /\ BetS A Z D.
Proof.
	intros A B C D.
	intros BetS_B_D_C.
	intros nCol_B_C_A.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq D D) as eq_D_D by (reflexivity).

	pose proof (cn_congruencereverse A D) as Cong_A_D_D_A.

	pose proof (lemma_s_col_eq_A_C A D A eq_A_A) as Col_A_D_A.
	pose proof (lemma_s_col_eq_B_C B D D eq_D_D) as Col_B_D_D.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_D_C) as BetS_C_D_B.
	pose proof (lemma_betweennotequal _ _ _ BetS_B_D_C) as (_ & neq_B_D & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_B_D_C) as (neq_D_C & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_B_D) as neq_D_B.
	pose proof (lemma_inequalitysymmetric _ _ neq_D_C) as neq_C_D.

	pose proof (lemma_s_col_BetS_A_B_C B D C BetS_B_D_C) as Col_B_D_C.
	pose proof (lemma_collinearorder _ _ _ Col_B_D_C) as (Col_D_B_C & Col_D_C_B & Col_C_B_D & Col_B_C_D & Col_C_D_B).


	pose proof (lemma_s_ncol_n_col _ _ _ nCol_B_C_A) as n_Col_B_C_A.
	pose proof (lemma_NCdistinct _ _ _ nCol_B_C_A) as (neq_B_C & neq_C_A & neq_B_A & neq_C_B & neq_A_C & neq_A_B).
	pose proof (lemma_NCorder _ _ _ nCol_B_C_A) as (nCol_C_B_A & nCol_C_A_B & nCol_A_B_C & nCol_B_A_C & nCol_A_C_B).

	epose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_C_A Col_B_C_D neq_B_D) as nCol_B_D_A.
	pose proof (lemma_NCdistinct _ _ _ nCol_B_D_A) as (_ & neq_D_A & _ & _ & neq_A_D & _).
	pose proof (lemma_NCorder _ _ _ nCol_B_D_A) as (nCol_D_B_A & nCol_D_A_B & nCol_A_B_D & nCol_B_A_D & nCol_A_D_B).

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_D_A) as CongA_B_D_A_A_D_B.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_D_B) as CongA_A_D_B_B_D_A.

	pose proof (proposition_10 _ _ neq_A_D) as (M & BetS_A_M_D & Cong_M_A_M_D).

	assert (eq M M) as eq_M_M by (reflexivity).

	pose proof (lemma_s_col_eq_A_C A M A eq_A_A) as Col_A_M_A.
	pose proof (lemma_s_col_eq_B_C B M M eq_M_M) as Col_B_M_M.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_M_D) as BetS_D_M_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_M_D) as (_ & neq_A_M & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_M_D) as (neq_M_D & _ & _).

	pose proof (lemma_s_col_BetS_A_B_C A M D BetS_A_M_D) as Col_A_M_D.
	pose proof (lemma_collinearorder _ _ _ Col_A_M_D) as (Col_M_A_D & Col_M_D_A & Col_D_A_M & Col_A_D_M & Col_D_M_A).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_M_A_M_D) as Cong_M_D_M_A.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_M_D_M_A) as (_ & Cong_D_M_M_A & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_M_A_M_D) as (_ & Cong_A_M_M_D & _).

	pose proof (lemma_NChelper _ _ _ _ _ nCol_B_D_A Col_B_D_C Col_B_D_D neq_C_D) as nCol_C_D_A.
	pose proof (lemma_NCorder _ _ _ nCol_C_D_A) as (nCol_D_C_A & nCol_D_A_C & nCol_A_C_D & nCol_C_A_D & nCol_A_D_C).
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_C_D_A) as CongA_C_D_A_A_D_C.


	pose proof (lemma_NChelper _ _ _ _ _ nCol_A_D_C Col_A_D_A Col_A_D_M neq_A_M) as nCol_A_M_C.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_M_C) as (_ & neq_M_C & _ & _ & neq_C_M & _).
	pose proof (lemma_NCorder _ _ _ nCol_A_M_C) as (nCol_M_A_C & nCol_M_C_A & nCol_C_A_M & nCol_A_C_M & nCol_C_M_A).

	pose proof (lemma_NChelper _ _ _ _ _ nCol_A_D_B Col_A_D_A Col_A_D_M neq_A_M) as nCol_A_M_B.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_M_B) as (_ & neq_M_B & _ & _ & neq_B_M & _).
	pose proof (lemma_NCorder _ _ _ nCol_A_M_B) as (nCol_M_A_B & nCol_M_B_A & nCol_B_A_M & nCol_A_B_M & nCol_B_M_A).

	pose proof (lemma_s_midpoint _ _ _ BetS_A_M_D Cong_A_M_M_D) as Midpoint_A_M_D.
	pose proof (lemma_s_midpoint _ _ _ BetS_D_M_A Cong_D_M_M_A) as Midpoint_D_M_A.

	pose proof (lemma_extension C M M C neq_C_M neq_M_C) as (E & BetS_C_M_E & Cong_M_E_M_C).

	assert (eq E E) as eq_E_E by (reflexivity).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_M_E) as BetS_E_M_C.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_M_E_M_C) as Cong_M_C_M_E.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_M_C_M_E) as (_ & Cong_C_M_M_E & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_C_M_M_E) as (Cong_M_C_E_M & _ & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_M_C_E_M) as Cong_E_M_M_C.

	pose proof (lemma_s_midpoint _ _ _ BetS_C_M_E Cong_C_M_M_E) as Midpoint_C_M_E.
	pose proof (lemma_s_midpoint _ _ _ BetS_E_M_C Cong_E_M_M_C) as Midpoint_E_M_C.

	pose proof (lemma_extension B M M B neq_B_M neq_M_B) as (F & BetS_B_M_F & Cong_M_F_M_B).

	assert (eq F F) as eq_F_F by (reflexivity).

	pose proof (lemma_s_col_eq_B_C F A A eq_A_A) as Col_F_A_A.

	pose proof (lemma_betweennotequal _ _ _ BetS_B_M_F) as (neq_M_F & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_M_F) as neq_F_M.

	pose proof (lemma_s_col_BetS_A_B_C B M F BetS_B_M_F) as Col_B_M_F.
	pose proof (lemma_collinearorder _ _ _ Col_B_M_F) as (Col_M_B_F & Col_M_F_B & Col_F_B_M & Col_B_F_M & Col_F_M_B).

	pose proof (lemma_congruenceflip _ _ _ _ Cong_M_F_M_B) as (_ & _ & Cong_M_F_B_M).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_M_F_B_M) as Cong_B_M_M_F.

	pose proof (lemma_s_midpoint _ _ _ BetS_B_M_F Cong_B_M_M_F) as Midpoint_B_M_F.

	pose proof (lemma_NChelper _ _ _ _ _ nCol_B_M_A Col_B_M_F Col_B_M_M neq_F_M) as nCol_F_M_A.
	pose proof (lemma_NCorder _ _ _ nCol_F_M_A) as (nCol_M_F_A & nCol_M_A_F & nCol_A_F_M & nCol_F_A_M & nCol_A_M_F).

	pose proof (lemma_NChelper _ _ _ _ _ nCol_A_M_F Col_A_M_A Col_A_M_D neq_A_D) as nCol_A_D_F.
	pose proof (lemma_NCorder _ _ _ nCol_A_D_F) as (nCol_D_A_F & nCol_D_F_A & nCol_F_A_D & nCol_A_F_D & nCol_F_D_A).

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_F_A_D) as CongA_F_A_D_D_A_F.

	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_B_M_F Midpoint_D_M_A neq_B_D) as Cong_B_D_F_A.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_D_M_A Midpoint_C_M_E neq_D_C) as Cong_D_C_A_E.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_B_M_F Midpoint_C_M_E neq_B_C) as Cong_B_C_F_E.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_B_M_F Midpoint_A_M_D neq_B_A) as Cong_B_A_F_D.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_B_D_F_A) as (Cong_D_B_A_F & _ & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_D_B_A_F) as Cong_A_F_D_B.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_D_B_A_F) as (_ & Cong_B_D_A_F & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_B_D_A_F) as Cong_A_F_B_D.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_D_C_A_E) as (_ & _ & Cong_D_C_E_A).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_D_C_E_A) as Cong_E_A_D_C.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_B_A_F_D) as Cong_F_D_B_A.

	pose proof (lemma_betweennesspreserved _ _ _ _ _ _ Cong_B_D_F_A Cong_B_C_F_E Cong_D_C_A_E BetS_B_D_C) as BetS_F_A_E.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_A_E) as BetS_E_A_F.
	pose proof (lemma_betweennotequal _ _ _ BetS_E_A_F) as (neq_A_F & _ & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_A_F) as (_ & neq_E_A & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_E_A) as neq_A_E.

	pose proof (lemma_s_col_BetS_A_B_C E A F BetS_E_A_F) as Col_E_A_F.
	pose proof (lemma_collinearorder _ _ _ Col_E_A_F) as (Col_A_E_F & Col_A_F_E & Col_F_E_A & Col_E_F_A & Col_F_A_E).

	epose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_A_F_D Col_A_F_E neq_A_E) as nCol_A_E_D.
	pose proof (lemma_NCdistinct _ _ _ nCol_A_E_D) as (_ & neq_E_D & _ & _ & neq_D_E & _).
	pose proof (lemma_NCorder _ _ _ nCol_A_E_D) as (nCol_E_A_D & nCol_E_D_A & nCol_D_A_E & nCol_A_D_E & nCol_D_E_A).
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_D_A_E) as CongA_D_A_E_E_A_D.

	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_E_M_C Midpoint_D_M_A neq_E_D) as Cong_E_D_C_A.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_A_M_D Midpoint_E_M_C neq_A_E) as Cong_A_E_D_C.

	pose proof (lemma_s_onray_assert_ABB D C neq_D_C) as OnRay_D_C_C.
	pose proof (lemma_s_onray_assert_ABB D B neq_D_B) as OnRay_D_B_B.
	pose proof (lemma_s_onray_assert_ABB D A neq_D_A) as OnRay_D_A_A.
	pose proof (lemma_s_onray_assert_ABB A D neq_A_D) as OnRay_A_D_D.
	pose proof (lemma_s_onray_assert_ABB A E neq_A_E) as OnRay_A_E_E.
	pose proof (lemma_s_onray_assert_ABB A F neq_A_F) as OnRay_A_F_F.

	pose proof (lemma_s_conga _ _ _ _ _ _ _ _ _ _ OnRay_A_F_F OnRay_A_D_D OnRay_D_B_B OnRay_D_A_A Cong_A_F_D_B Cong_A_D_D_A Cong_F_D_B_A nCol_F_A_D) as CongA_F_A_D_B_D_A.
	pose proof (lemma_s_conga _ _ _ _ _ _ _ _ _ _ OnRay_A_E_E OnRay_A_D_D OnRay_D_C_C OnRay_D_A_A Cong_A_E_D_C Cong_A_D_D_A Cong_E_D_C_A nCol_E_A_D) as CongA_E_A_D_C_D_A.

	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_F_A_D_B_D_A CongA_B_D_A_A_D_B) as CongA_F_A_D_A_D_B.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_F_A_D_A_D_B) as CongA_A_D_B_F_A_D.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_D_B_F_A_D CongA_F_A_D_D_A_F) as CongA_A_D_B_D_A_F.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_D_B_D_A_F) as CongA_D_A_F_A_D_B.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_D_A_F_A_D_B CongA_A_D_B_B_D_A) as CongA_D_A_F_B_D_A.

	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_E_A_D_C_D_A CongA_C_D_A_A_D_C) as CongA_E_A_D_A_D_C.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_D_A_E_E_A_D CongA_E_A_D_C_D_A) as CongA_D_A_E_C_D_A.

	pose proof (lemma_s_os _ _ _ _ _ BetS_B_M_F Col_A_D_M nCol_A_D_B) as OS_B_A_D_F.
	pose proof (lemma_oppositesidesymmetric _ _ _ _ OS_B_A_D_F) as OS_F_A_D_B.

	pose proof (proposition_27 _ _ _ _ _ _ BetS_F_A_E BetS_C_D_B CongA_F_A_D_A_D_B OS_F_A_D_B) as Par_F_E_C_B.
	pose proof (lemma_parallelflip _ _ _ _ Par_F_E_C_B) as (_ & _ & Par_E_F_B_C).

	exists E, F, M.
	split.
	exact BetS_E_A_F.
	split.
	exact CongA_F_A_D_A_D_B.
	split.
	exact CongA_F_A_D_B_D_A.
	split.
	exact CongA_D_A_F_B_D_A.
	split.
	exact CongA_E_A_D_A_D_C.
	split.
	exact CongA_E_A_D_C_D_A.
	split.
	exact CongA_D_A_E_C_D_A.
	split.
	exact Par_E_F_B_C.
	split.
	exact Cong_E_A_D_C.
	split.
	exact Cong_A_F_B_D.
	split.
	exact Cong_A_M_M_D.
	split.
	exact Cong_E_M_M_C.
	split.
	exact Cong_B_M_M_F.
	split.
	exact BetS_E_M_C.
	split.
	exact BetS_B_M_F.
	exact BetS_A_M_D.
Qed.

End Euclid.
