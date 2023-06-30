Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_Euclid4.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NChelper.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence_smaller.
Require Import ProofCheckingEuclid.lemma_angletrichotomy_n_CongA_ABC_DEF_n_LtA_DEF_ABC_LtA_ABC_DEF.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_collinearparallel.
Require Import ProofCheckingEuclid.lemma_collinearright.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_crossbar2.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_oppositesidesymmetric.
Require Import ProofCheckingEuclid.lemma_parallelflip.
Require Import ProofCheckingEuclid.lemma_parallelsymmetric.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_right_triangle_CBA_n_ACB.
Require Import ProofCheckingEuclid.lemma_right_triangle_NC.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_meet.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_par.
Require Import ProofCheckingEuclid.lemma_s_right_triangle.
Require Import ProofCheckingEuclid.lemma_s_ss.
Require Import ProofCheckingEuclid.lemma_s_sumtwort.
Require Import ProofCheckingEuclid.lemma_s_supp.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.
Require Import ProofCheckingEuclid.lemma_supplement_symmetric.
Require Import ProofCheckingEuclid.lemma_supplementinequality.
Require Import ProofCheckingEuclid.lemma_supplements_conga.
Require Import ProofCheckingEuclid.lemma_twoperpsparallel.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_15a.
Require Import ProofCheckingEuclid.proposition_27.
Require Import ProofCheckingEuclid.proposition_29.
Require Import ProofCheckingEuclid.proposition_31.
Require Import ProofCheckingEuclid.proposition_33B.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma aaa :
	forall A B C D,
	RightTriangle A B C ->
	RightTriangle B C D ->
    Cong A B B C ->
    Cong B C C D ->
    SS D A B C ->
    Cong A B D A /\ RightTriangle D A B /\ RightTriangle C D A.
Proof.
    intros A B C D.
    intros RightTriangle_A_B_C.
    intros RightTriangle_B_C_D.
    intros Cong_A_B_B_C.
    intros Cong_B_C_C_D.
    intros SS_D_A_B_C.


	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).

    pose proof (lemma_s_col_eq_A_C B C B eq_B_B) as Col_B_C_B.
    pose proof (lemma_s_col_eq_A_C C B C eq_C_C) as Col_C_B_C.
    pose proof (lemma_s_col_eq_B_C B C C eq_C_C) as Col_B_C_C.

    pose proof (cn_congruencereverse B C) as Cong_B_C_C_B.

    pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_A_B_C) as nCol_A_B_C.
    pose proof (lemma_right_triangle_NC _ _ _ RightTriangle_B_C_D) as nCol_B_C_D.

    pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_A_B_C) as RightTriangle_C_B_A.
    pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_B_C_D) as RightTriangle_D_C_B.

    pose proof (lemma_right_triangle_CBA_n_ACB _ _ _ RightTriangle_A_B_C) as n_RightTriangle_C_A_B.
    pose proof (lemma_right_triangle_CBA_n_ACB _ _ _ RightTriangle_C_B_A) as n_RightTriangle_A_C_B.

    epose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_A_B_C RightTriangle_D_C_B) as CongA_A_B_C_D_C_B.

    pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_A_B_B_C Cong_B_C_C_D) as Cong_A_B_C_D.
    pose proof (lemma_congruenceflip _ _ _ _ Cong_A_B_C_D) as (Cong_B_A_D_C & Cong_B_A_C_D & Cong_A_B_D_C).

    pose proof (lemma_samesidesymmetric _ _ _ _ SS_D_A_B_C) as (SS_A_D_B_C & SS_D_A_C_B & SS_A_D_C_B).

    pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).
    pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).

    pose proof (lemma_NCdistinct _ _ _ nCol_B_C_D) as (_ & neq_C_D & neq_B_D & _ & neq_D_C & neq_D_B).
    pose proof (lemma_NCorder _ _ _ nCol_B_C_D) as (nCol_C_B_D & nCol_C_D_B & nCol_D_B_C & nCol_B_D_C & nCol_D_C_B).

    (* can be replaced with parallelNC *)
    assert (~ eq A D) as neq_A_D.
    {
        intro eq_A_D.
        assert (RightTriangle A C B) as RightTriangle_A_C_B by (rewrite eq_A_D; exact RightTriangle_D_C_B).

        contradict RightTriangle_A_C_B.
        exact n_RightTriangle_A_C_B.
    }
    pose proof (lemma_inequalitysymmetric _ _ neq_A_D) as neq_D_A.

    pose proof (postulate_Euclid2 _ _ neq_A_D) as (E & BetS_A_D_E).
    pose proof (postulate_Euclid2 _ _ neq_B_C) as (H & BetS_B_C_H).

    pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_E) as BetS_E_D_A.
    pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_C_H) as BetS_H_C_B.
    pose proof (lemma_betweennotequal _ _ _ BetS_A_D_E) as (neq_D_E & _ & neq_A_E).
    pose proof (lemma_betweennotequal _ _ _ BetS_B_C_H) as (neq_C_H & _ & neq_B_H).
    pose proof (lemma_betweennotequal _ _ _ BetS_E_D_A) as (_ & neq_E_D & neq_E_A).
    pose proof (lemma_betweennotequal _ _ _ BetS_H_C_B) as (_ & neq_H_C & neq_H_B).
    
    pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_D_E) as Col_A_D_E.
    pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_B_C_H) as Col_B_C_H.

    pose proof (lemma_collinearorder _ _ _ Col_A_D_E) as (Col_D_A_E & Col_D_E_A & Col_E_A_D & Col_A_E_D & Col_E_D_A).
    pose proof (lemma_collinearorder _ _ _ Col_B_C_H) as (Col_C_B_H & Col_C_H_B & Col_H_B_C & Col_B_H_C & Col_H_C_B).



    pose proof (lemma_twoperpsparallel _ _ _ _ RightTriangle_A_B_C RightTriangle_B_C_D SS_A_D_B_C) as Par_A_B_C_D.
    pose proof (lemma_parallelflip _ _ _ _ Par_A_B_C_D) as (Par_B_A_C_D & Par_A_B_D_C & Par_B_A_D_C).

    epose proof (proposition_33B _ _ _ _ Par_A_B_D_C Cong_A_B_D_C SS_A_D_B_C) as (Par_A_D_B_C & Cong_A_D_B_C).

    pose proof (lemma_parallelflip _ _ _ _ Par_A_D_B_C) as (Par_D_A_B_C & Par_A_D_C_B & Par_D_A_C_B).

    epose proof (lemma_collinearparallel _ _ _ _ _ Par_D_A_C_B Col_C_B_H neq_H_B) as Par_D_A_H_B.
    pose proof (lemma_parallelsymmetric _ _ _ _ Par_D_A_H_B) as Par_H_B_D_A.
    epose proof (lemma_collinearparallel _ _ _ _ _ Par_H_B_D_A Col_D_A_E neq_E_A) as Par_H_B_E_A.
    pose proof (lemma_parallelsymmetric _ _ _ _ Par_H_B_E_A) as Par_E_A_H_B.
    pose proof (lemma_parallelflip _ _ _ _ Par_E_A_H_B) as (Par_A_E_H_B & Par_E_A_B_H & Par_A_E_B_H).


    pose proof (postulate_Euclid2 _ _ neq_C_D) as (F & BetS_C_D_F).
    pose proof (postulate_Euclid2 _ _ neq_B_A) as (G & BetS_B_A_G).


    pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_D_F) as BetS_F_D_C.
    pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_G) as BetS_G_A_B.
    pose proof (lemma_betweennotequal _ _ _ BetS_C_D_F) as (neq_D_F & _ & neq_C_F).
    pose proof (lemma_betweennotequal _ _ _ BetS_B_A_G) as (neq_A_G & _ & neq_B_G).
    pose proof (lemma_inequalitysymmetric _ _ neq_D_F) as neq_F_D.
    pose proof (lemma_inequalitysymmetric _ _ neq_C_F) as neq_F_C.
    pose proof (lemma_inequalitysymmetric _ _ neq_B_G) as neq_G_B.

    pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_C_D_F) as Col_C_D_F.
    pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_B_A_G) as Col_B_A_G.
    pose proof (lemma_collinearorder _ _ _ Col_C_D_F) as (Col_D_C_F & Col_D_F_C & Col_F_C_D & Col_C_F_D & Col_F_D_C).
    pose proof (lemma_collinearorder _ _ _ Col_B_A_G) as (Col_A_B_G & Col_A_G_B & Col_G_B_A & Col_B_G_A & Col_G_A_B).

    epose proof (lemma_collinearparallel _ _ _ _ _ Par_A_B_D_C Col_D_C_F neq_F_C) as Par_A_B_F_C.
    pose proof (lemma_parallelsymmetric _ _ _ _ Par_A_B_F_C) as Par_F_C_A_B.

    epose proof (lemma_collinearparallel _ _ _ _ _ Par_F_C_A_B Col_A_B_G neq_G_B) as Par_F_C_G_B.

    assert (OS A D C H) as OS_A_D_C_H.
    admit.

    epose proof (proposition_29 A E B H _ D C Par_A_E_B_H BetS_A_D_E BetS_B_C_H BetS_F_D_C OS_A_D_C_H) as (CongA_A_D_C_D_C_H & CongA_F_D_E_D_C_H & SumTwoRT_E_D_C_D_C_H).

    assert (OS F D A B) as OS_F_D_A_B.
    admit.
    epose proof (proposition_29 _ _ _ _ _ _ _ Par_F_C_G_B BetS_F_D_C BetS_G_A_B BetS_E_D_A OS_F_D_A_B) as (CongA_F_D_A_D_A_B & CongA_E_D_C_D_A_B & SumTwoRT_C_D_A_D_A_B).

Qed.

End Euclid.
