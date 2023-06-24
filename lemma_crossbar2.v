Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_crossbar.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_shared_initial_point.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_lta.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_ss.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_sameside_onray_EFAC_BFG_EGAC.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_07.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_crossbar2 :
	forall A G H P S T,
	LtA H G A H G P ->
	SS A P G H ->
	OnRay G H S ->
	OnRay G P T ->
	exists X, BetS T X S /\ OnRay G A X.
Proof.
	intros A G H P S T.
	intros LtA_H_G_A_H_G_P.
	intros SS_A_P_G_H.
	intros OnRay_G_H_S.
	intros OnRay_G_P_T.

	destruct LtA_H_G_A_H_G_P as (L & K & J & BetS_L_K_J & OnRay_G_H_L & OnRay_G_P_J & CongA_H_G_A_H_G_K).
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_H_G_A_H_G_K) as nCol_H_G_K.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_H_G_K) as n_Col_H_G_K.


	assert (SS_A_P_G_H_2 := SS_A_P_G_H).
	destruct SS_A_P_G_H_2 as (_ & _ & _ & _ & _ & _ & _ &  _ & nCol_G_H_P).
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_G_H_P) as n_Col_G_H_P.


	assert (~ Col L G J) as n_Col_L_G_J.
	{
		intro Col_L_G_J.
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_G_H_L) as Col_G_H_L.
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_G_P_J) as Col_G_P_J.
		pose proof (lemma_collinearorder _ _ _ Col_G_H_L) as (_ & _ & Col_L_G_H & _ & _).
		pose proof (lemma_onray_strict _ _ _ OnRay_G_H_L) as neq_G_L.
		pose proof (lemma_inequalitysymmetric _ _ neq_G_L) as neq_L_G.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_L_G_J Col_L_G_H neq_L_G) as Col_G_J_H.
		pose proof (lemma_collinearorder _ _ _ Col_G_J_H) as (Col_J_G_H & _ & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_G_P_J) as (_ & _ & Col_J_G_P & _ & _).
		pose proof (lemma_onray_strict _ _ _ OnRay_G_P_J) as neq_G_J.
		pose proof (lemma_inequalitysymmetric _ _ neq_G_J) as neq_J_G.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_J_G_H Col_J_G_P neq_J_G) as Col_G_H_P.
		contradict Col_G_H_P.
		exact n_Col_G_H_P.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_L_G_J) as nCol_L_G_J.

	pose proof (lemma_s_triangle _ _ _ nCol_L_G_J) as Triangle_L_G_J.
	pose proof (lemma_onray_shared_initial_point _ _ _ _ OnRay_G_P_J OnRay_G_P_T) as OnRay_G_J_T.
	pose proof (lemma_onray_shared_initial_point _ _ _ _ OnRay_G_H_L OnRay_G_H_S) as OnRay_G_L_S.

	pose proof (lemma_crossbar _ _ _ _ _ _ Triangle_L_G_J BetS_L_K_J OnRay_G_L_S OnRay_G_J_T) as (M & OnRay_G_K_M & BetS_S_M_T).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_S_M_T) as BetS_T_M_S.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_H_G_A_H_G_K) as CongA_H_G_K_H_G_A.
	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_H_G_A_H_G_K) as (_ & neq_G_A & _ & _ & _ & _).
	pose proof (lemma_onray_strict _ _ _ OnRay_G_K_M) as neq_G_M.
	pose proof (lemma_layoff _ _ _ _ neq_G_A neq_G_M) as (N & OnRay_G_A_N & Cong_G_N_G_M).
	assert (eq H H) as eq_H_H by (reflexivity).

	assert (~ eq G H) as n_eq_G_H.
	{
		intro eq_G_H.
		pose proof (lemma_s_col_eq_A_B G H P eq_G_H) as Col_G_H_P.
		contradict Col_G_H_P.
		exact n_Col_G_H_P.
	}
	assert (neq_G_H := n_eq_G_H).


	pose proof (lemma_s_onray_assert_ABB G H neq_G_H) as OnRay_G_H_H.

	assert (~ Col H G M) as n_Col_H_G_M.
	{
		intro Col_H_G_M.
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_G_K_M) as Col_G_K_M.
		pose proof (lemma_collinearorder _ _ _ Col_G_K_M) as (_ & _ & Col_M_G_K & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_H_G_M) as (_ & _ & _ & _ & Col_M_G_H).
		pose proof (lemma_inequalitysymmetric _ _ neq_G_M) as neq_M_G.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_M_G_K Col_M_G_H neq_M_G) as Col_G_K_H.
		pose proof (lemma_collinearorder _ _ _ Col_G_K_H) as (_ & _ & Col_H_G_K & _ & _).
		contradict Col_H_G_K.
		exact n_Col_H_G_K.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_H_G_M) as nCol_H_G_M.

	pose proof (lemma_equalanglesreflexive _ _ _ nCol_H_G_M) as CongA_H_G_M_H_G_M.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_G_K_M) as OnRay_G_M_K.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_H_G_M_H_G_M OnRay_G_H_H OnRay_G_M_K) as CongA_H_G_M_H_G_K.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_H_G_M_H_G_K CongA_H_G_K_H_G_A) as CongA_H_G_M_H_G_A.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_H_G_K_H_G_A) as nCol_H_G_A.
	pose proof (lemma_equalanglesreflexive _ _ _ nCol_H_G_A) as CongA_H_G_A_H_G_A.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_H_G_A_H_G_A OnRay_G_H_H OnRay_G_A_N) as CongA_H_G_A_H_G_N.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_H_G_M_H_G_A CongA_H_G_A_H_G_N) as CongA_H_G_M_H_G_N.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_H_G_M_H_G_N) as CongA_H_G_N_H_G_M.
	pose proof (cn_congruencereflexive G H) as Cong_G_H_G_H.
	pose proof (proposition_04 _ _ _ _ _ _ Cong_G_H_G_H Cong_G_N_G_M CongA_H_G_N_H_G_M) as (Cong_H_N_H_M & _ & _).
	assert (eq G G) as eq_G_G by (reflexivity).
	pose proof (lemma_s_col_eq_A_B G G H eq_G_G) as Col_G_G_H.
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SS_A_P_G_H Col_G_G_H OnRay_G_P_T) as SS_A_T_G_H.
	pose proof (lemma_betweennotequal _ _ _ BetS_S_M_T) as (_ & neq_S_M & _).
	
	pose proof (lemma_s_onray_assert_bets_ABE S M T BetS_S_M_T neq_S_M) as OnRay_S_M_T.

	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_S_M_T) as OnRay_S_T_M.
	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_G_H_S) as Col_G_H_S.
	pose proof (lemma_collinearorder _ _ _ Col_G_H_S) as (_ & _ & _ & Col_G_S_H & _).
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SS_A_T_G_H Col_G_S_H OnRay_S_T_M) as SS_A_M_G_H.
	pose proof (lemma_samesidesymmetric _ _ _ _ SS_A_M_G_H) as (SS_M_A_G_H & _ & _).
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SS_M_A_G_H Col_G_G_H OnRay_G_A_N) as SS_M_N_G_H.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_H_N_H_M) as (Cong_N_H_M_H & _ & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_N_H_M_H) as Cong_M_H_N_H.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_G_N_G_M) as (Cong_N_G_M_G & _ & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_N_G_M_G) as Cong_M_G_N_G.
	pose proof (proposition_07 _ _ _ _ neq_G_H Cong_M_G_N_G Cong_M_H_N_H SS_M_N_G_H) as eq_M_N.
	pose proof (lemma_equalitysymmetric _ _ eq_M_N) as eq_N_M.
	assert (OnRay G A M) as OnRay_G_A_M by (rewrite eq_M_N; exact OnRay_G_A_N).

	exists M.
	split.
	exact BetS_T_M_S.
	exact OnRay_G_A_M.

Qed.

End Euclid.

