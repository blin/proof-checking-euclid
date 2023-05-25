Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_lessthancongruence_smaller.
Require Import ProofCheckingEuclid.lemma_lessthannotequal.
Require Import ProofCheckingEuclid.lemma_ondiameter.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_outcirc_beyond_perimeter.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_subtractequals.
Require Import ProofCheckingEuclid.lemma_together.
Require Import ProofCheckingEuclid.lemma_trichotomy_asymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_22 :
	forall A B C E F a b c,
	TogetherGreater A a B b C c ->
	TogetherGreater A a C c B b ->
	TogetherGreater B b C c A a ->
	neq F E ->
	exists X Y, Cong F X B b /\ Cong F Y A a /\ Cong X Y C c /\ OnRay F E X /\ Triangle F X Y.
Proof.
	intros A B C E F a b c.
	intros TogetherGreater_A_a_B_b_C_c.
	intros TogetherGreater_A_a_C_c_B_b.
	intros TogetherGreater_B_b_C_c_A_a.
	intros neq_F_E.

	assert (TogetherGreater_A_a_B_b_C_c2 := TogetherGreater_A_a_B_b_C_c).
	destruct TogetherGreater_A_a_B_b_C_c2 as (P & BetS_A_a_P & Cong_a_P_B_b & Lt_C_c_A_P).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_a_P) as (neq_a_P  & neq_A_a & _).
	pose proof (axiom_nocollapse _ _ _ _ neq_a_P Cong_a_P_B_b) as neq_B_b.
	pose proof (lemma_lessthannotequal _ _ _ _ Lt_C_c_A_P) as (neq_C_c & _).

	pose proof (lemma_layoff _ _ _ _ neq_F_E neq_B_b) as (G & OnRay_F_E_G & Cong_F_G_B_b).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_F_G_B_b) as Cong_B_b_F_G.
	pose proof (axiom_nocollapse _ _ _ _ neq_B_b Cong_B_b_F_G) as neq_F_G.
	pose proof (lemma_inequalitysymmetric _ _ neq_F_G) as neq_G_F.

	pose proof (lemma_extension F G C c neq_F_G neq_C_c) as (H & BetS_F_G_H & Cong_G_H_C_c).
	pose proof (lemma_extension G F A a neq_G_F neq_A_a) as (D & BetS_G_F_D & Cong_F_D_A_a).
	
	pose proof (lemma_congruenceflip F D A a Cong_F_D_A_a) as (_ & Cong_D_F_A_a & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_F_D) as BetS_D_F_G.
	pose proof (lemma_betweennotequal _ _ _ BetS_G_F_D) as (neq_F_D & _ & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_F_G_H) as (neq_G_H & _ & _).

	pose proof (cn_congruencereflexive C c) as Cong_C_c_C_c.
	pose proof (cn_congruencereflexive F D) as Cong_F_D_F_D.
	pose proof (cn_congruencereflexive G H) as Cong_G_H_G_H.
	pose proof (cn_congruencereverse D G) as Cong_D_G_G_D.

	epose proof (lemma_together _ _ _ F _ H D F _ _ _ TogetherGreater_B_b_C_c_A_a Cong_F_G_B_b Cong_G_H_C_c BetS_F_G_H Cong_D_F_A_a) as (Lt_D_F_F_H & _).
	destruct Lt_D_F_F_H as (M & BetS_F_M_H & Cong_F_M_D_F).

	pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_D_F_G BetS_F_G_H) as BetS_D_F_H.
	pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_D_F_H BetS_F_M_H) as BetS_D_F_M.
	pose proof (lemma_betweennotequal _ _ _ BetS_F_M_H) as (_ & neq_F_M & _).

	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_F_M_D_F Cong_D_F_A_a) as Cong_F_M_A_a.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_F_M_A_a) as Cong_A_a_F_M.

	pose proof (lemma_extension F M C c neq_F_M neq_C_c) as (J & BetS_F_M_J & Cong_M_J_C_c).

	epose proof (lemma_together A C _ F M J F G a c _ TogetherGreater_A_a_C_c_B_b Cong_F_M_A_a Cong_M_J_C_c BetS_F_M_J Cong_F_G_B_b) as (Lt_F_G_F_J & _).
	epose proof (lemma_together _ _ _ _ _ _ _ _ _ _ _ TogetherGreater_A_a_B_b_C_c Cong_D_F_A_a Cong_F_G_B_b BetS_D_F_G Cong_C_c_C_c) as (Lt_C_c_D_G & _).

	pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_C_c_D_G Cong_D_G_G_D) as Lt_C_c_G_D.

	destruct Lt_C_c_G_D as (N & BetS_G_N_D & Cong_G_N_C_c).
	destruct Lt_F_G_F_J as (Q & BetS_F_Q_J & Cong_F_Q_F_G).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_F_D_A_a) as Cong_A_a_F_D.
	pose proof (cn_congruencetransitive _ _ _ _ _ _ Cong_A_a_F_M Cong_A_a_F_D) as Cong_F_M_F_D.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_M_J_C_c) as Cong_C_c_M_J.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_G_N_C_c Cong_C_c_M_J) as Cong_G_N_M_J.
	pose proof (lemma_congruenceflip G N M J Cong_G_N_M_J) as (_ & Cong_N_G_M_J & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_G_H_C_c) as Cong_C_c_G_H.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_G_N_C_c) as Cong_C_c_G_N.
	pose proof (cn_congruencetransitive _ _ _ _ _ _ Cong_C_c_G_N Cong_C_c_G_H) as Cong_G_N_G_H.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_N_D) as BetS_D_N_G.
	pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_D_F_M BetS_F_M_J) as BetS_D_F_J.
	pose proof (lemma_betweennotequal _ _ _ BetS_F_M_J) as (_ & _ & neq_F_J).
	pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_D_F_M BetS_F_M_J) as BetS_D_M_J.

	pose proof (lemma_s_onray_assert_bets_AEB F J Q BetS_F_Q_J neq_F_J) as OnRay_F_J_Q.
	pose proof (lemma_s_onray _ _ _ _ BetS_D_F_G BetS_D_F_J) as OnRay_F_G_J.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_F_G_J) as OnRay_F_J_G.
	pose proof (lemma_layoffunique _ _ _ _ OnRay_F_J_Q OnRay_F_J_G Cong_F_Q_F_G) as eq_Q_G.
	pose proof (lemma_equalitysymmetric _ _ eq_Q_G) as eq_G_Q.
	assert (BetS F G J) as BetS_F_G_J by (rewrite eq_G_Q; exact BetS_F_Q_J).
	pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_D_F_G BetS_F_G_J) as BetS_D_G_J.
	pose proof (lemma_subtractequals _ _ _ _ _ BetS_D_N_G BetS_D_M_J Cong_N_G_M_J BetS_D_G_J) as BetS_D_N_M.


	pose proof (postulate_Euclid3 _ _ neq_F_D) as (L & CI_L_F_F_D).
	pose proof (postulate_Euclid3 _ _ neq_G_H) as (R & CI_R_G_G_H).

	pose proof (lemma_s_outcirc_beyond_perimeter _ _ _ _ _ _ CI_L_F_F_D BetS_F_M_H Cong_F_M_F_D) as OutCirc_H_L.
	pose proof (lemma_ondiameter _ _ _ _ _ _ _ CI_L_F_F_D Cong_F_D_F_D Cong_F_M_F_D BetS_D_F_M BetS_D_N_M) as InCirc_N_L.

	pose proof (lemma_s_oncirc_radius _ _ _ _ _ CI_R_G_G_H Cong_G_H_G_H) as OnCirc_H_R.
	pose proof (lemma_s_oncirc_radius _ _ _ _ _ CI_R_G_G_H Cong_G_N_G_H) as OnCirc_N_R.

	epose proof (postulate_circle_circle _ _ _ _ L R _ _ _ _ CI_L_F_F_D InCirc_N_L OutCirc_H_L CI_R_G_G_H OnCirc_N_R OnCirc_H_R) as (K & OnCirc_K_L & OnCirc_K_R).

	pose proof (axiom_circle_center_radius _ _ _ _ _ CI_L_F_F_D OnCirc_K_L) as Cong_F_K_F_D.
	pose proof (axiom_circle_center_radius _ _ _ _ _ CI_R_G_G_H OnCirc_K_R) as Cong_G_K_G_H.

	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_F_K_F_D Cong_F_D_A_a) as Cong_F_K_A_a.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_G_K_G_H Cong_G_H_C_c) as Cong_G_K_C_c.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_F_K_A_a) as Cong_A_a_F_K.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_G_K_C_c) as Cong_C_c_G_K.
	pose proof (lemma_congruenceflip F K A a Cong_F_K_A_a) as (_ & Cong_K_F_A_a & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_K_F_A_a) as Cong_A_a_K_F.

	pose proof (axiom_nocollapse _ _ _ _ neq_A_a Cong_A_a_F_K) as neq_F_K.
	pose proof (axiom_nocollapse _ _ _ _ neq_C_c Cong_C_c_G_K) as neq_G_K.


	assert (~ Col F G K) as n_Col_F_G_K.
	{
		intro Col_F_G_K.
		(* assert by cases *)
		assert (nCol F G K) as nCol_F_G_K.
		destruct Col_F_G_K as [eq_F_G | [eq_F_K | [eq_G_K | [BetS_G_F_K | [BetS_F_G_K | BetS_F_K_G]]]]].
		{
			(* case eq_F_G *)
			contradict eq_F_G.
			exact neq_F_G.
		}
		{
			(* case eq_F_K *)
			contradict eq_F_K.
			exact neq_F_K.
		}
		{
			(* case eq_G_K *)
			contradict eq_G_K.
			exact neq_G_K.
		}
		{
			(* case BetS_G_F_K *)
			destruct TogetherGreater_A_a_B_b_C_c as (S & BetS_A_a_S & Cong_a_S_B_b & Lt_C_c_A_S).
			pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_a_S_B_b Cong_B_b_F_G) as Cong_a_S_F_G.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_F_K) as BetS_K_F_G.
			pose proof (cn_sumofparts _ _ _ _ _ _ Cong_A_a_K_F Cong_a_S_F_G BetS_A_a_S BetS_K_F_G) as Cong_A_S_K_G.
			pose proof (lemma_congruenceflip A S K G Cong_A_S_K_G) as (_ & _ & Cong_A_S_G_K).
			pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_C_c_A_S Cong_A_S_G_K) as Lt_C_c_G_K.
			pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_C_c_G_K Cong_C_c_G_K) as Lt_G_K_G_K.
			pose proof (lemma_trichotomy_asymmetric _ _ _ _ Lt_G_K_G_K) as n_Lt_G_K_G_K.

			contradict Lt_G_K_G_K.
			exact n_Lt_G_K_G_K.
		}
		{
			(* case BetS_F_G_K *)
			destruct TogetherGreater_B_b_C_c_A_a as (S & BetS_B_b_S & Cong_b_S_C_c & Lt_A_a_B_S).
			pose proof (lemma_congruencesymmetric _ _ _ _ Cong_b_S_C_c) as Cong_C_c_b_S.
			pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_G_K_C_c Cong_C_c_b_S) as Cong_G_K_b_S.
			pose proof (cn_sumofparts _ _ _ _ _ _ Cong_F_G_B_b Cong_G_K_b_S BetS_F_G_K BetS_B_b_S) as Cong_F_K_B_S.
			pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_A_a_B_S Cong_A_a_F_K) as Lt_F_K_B_S.
			pose proof (lemma_congruencesymmetric _ _ _ _ Cong_F_K_B_S) as Cong_B_S_F_K.
			pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_F_K_B_S Cong_B_S_F_K) as Lt_F_K_F_K.
			pose proof (lemma_trichotomy_asymmetric _ _ _ _ Lt_F_K_F_K) as n_Lt_F_K_F_K.

			contradict Lt_F_K_F_K.
			exact n_Lt_F_K_F_K.
		}
		{
			(* case BetS_F_K_G *)
			
			destruct TogetherGreater_A_a_C_c_B_b as (S & BetS_A_a_S & Cong_a_S_C_c & Lt_B_b_A_S).
			pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_B_b_A_S Cong_B_b_F_G) as Lt_F_G_A_S.
			pose proof (lemma_congruencesymmetric _ _ _ _ Cong_a_S_C_c) as Cong_C_c_a_S.
			pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_G_K_C_c Cong_C_c_a_S) as Cong_G_K_a_S.
			pose proof (lemma_congruenceflip G K a S Cong_G_K_a_S) as (_ & Cong_K_G_a_S & _).
			pose proof (cn_sumofparts _ _ _ _ _ _ Cong_F_K_A_a Cong_K_G_a_S BetS_F_K_G BetS_A_a_S) as Cong_F_G_A_S.
			pose proof (lemma_congruencesymmetric _ _ _ _ Cong_F_G_A_S) as Cong_A_S_F_G.
			pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_F_G_A_S Cong_A_S_F_G) as Lt_F_G_F_G.
			pose proof (lemma_trichotomy_asymmetric _ _ _ _ Lt_F_G_F_G) as n_Lt_F_G_F_G.

			contradict Lt_F_G_F_G.
			exact n_Lt_F_G_F_G.
		}
		pose proof (lemma_s_ncol_n_col _ _ _ nCol_F_G_K) as n_Col_F_G_K.

		contradict Col_F_G_K.
		exact n_Col_F_G_K.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_F_G_K) as nCol_F_G_K.

	pose proof (lemma_s_triangle _ _ _ nCol_F_G_K) as Triangle_F_G_K.

	exists G, K.
	split.
	exact Cong_F_G_B_b.
	split.
	exact Cong_F_K_A_a.
	split.
	exact Cong_G_K_C_c.
	split.
	exact OnRay_F_E_G.
	exact Triangle_F_G_K.
Qed.

End Euclid.
