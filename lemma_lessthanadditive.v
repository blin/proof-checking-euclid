Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_lessthancongruence_smaller.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_outerconnectivity.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_lt.
Require Import ProofCheckingEuclid.lemma_s_lta.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_trichotomy_asymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_lessthanadditive :
	forall A B C D E F,
	Lt A B C D ->
	BetS A B E ->
	BetS C D F ->
	Cong B E D F ->
	Lt A E C F.
Proof.
	intros A B C D E F.
	intros Lt_A_B_C_D.
	intros BetS_A_B_E.
	intros BetS_C_D_F.
	intros Cong_B_E_D_F.

	destruct Lt_A_B_C_D as (b & BetS_C_b_D & Cong_C_b_A_B).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_C_b_A_B) as Cong_A_B_C_b.
	pose proof (lemma_betweennotequal _ _ _ BetS_C_b_D) as (_ & neq_C_b & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_C_b) as neq_b_C.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_E) as (neq_B_E & _ & _).
	pose proof (lemma_extension _ _ _ _ neq_C_b neq_B_E) as (e & BetS_C_b_e & Cong_b_e_B_E).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_b_e_B_E) as Cong_B_E_b_e.
	epose proof (cn_sumofparts A _ E C _ e Cong_A_B_C_b Cong_B_E_b_e BetS_A_B_E BetS_C_b_e) as Cong_A_E_C_e.
	pose proof (cn_congruencereflexive e D) as Cong_e_D_e_D.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_b_e) as BetS_e_b_C.
	pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_C_b_D BetS_C_D_F) as BetS_C_b_F.

	assert (~ BetS b F e) as n_BetS_b_F_e.
	{
		intro BetS_b_F_e.
		pose proof (cn_congruencereflexive b F) as Cong_b_F_b_F.
		pose proof (lemma_s_lt _ _ _ _ _ BetS_b_F_e Cong_b_F_b_F) as Lt_b_F_b_e.
		pose proof (cn_congruencereflexive F D) as Cong_F_D_F_D.
		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_C_b_D BetS_C_D_F) as BetS_b_D_F.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_b_D_F) as BetS_F_D_b.
		pose proof (lemma_s_lt _ _ _ _ _ BetS_F_D_b Cong_F_D_F_D) as Lt_F_D_F_b.
		pose proof (cn_congruencereverse F b) as Cong_F_b_b_F.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_F_D_F_b Cong_F_b_b_F) as Lt_F_D_b_F.
		pose proof (cn_congruencereverse F D) as Cong_F_D_D_F.
		pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_F_D_b_F Cong_F_D_D_F) as Lt_D_F_b_F.
		pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_b_e_B_E Cong_B_E_D_F) as Cong_b_e_D_F.
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_b_e_D_F) as Cong_D_F_b_e.
		pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_D_F_b_F Cong_D_F_b_e) as Lt_b_e_b_F.
		destruct Lt_b_e_b_F as (q & BetS_b_q_F & Cong_b_q_b_e).
		pose proof (lemma_betweennotequal _ _ _ BetS_b_q_F) as (_ & neq_b_q & _).
		pose proof (lemma_betweennotequal _ _ _ BetS_C_b_F) as (neq_b_F & _ & _).
		pose proof (lemma_s_onray_assert_bets_AEB b F q BetS_b_q_F neq_b_F) as OnRay_b_F_q.
		pose proof (lemma_s_onray_assert_bets_ABE b F e BetS_b_F_e neq_b_F) as OnRay_b_F_e.
		pose proof (lemma_layoffunique _ _ _ _ OnRay_b_F_q OnRay_b_F_e Cong_b_q_b_e) as eq_q_e.
		
		assert (BetS b e F) as BetS_b_e_F by (rewrite <- eq_q_e; exact BetS_b_q_F).

		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_b_F_e BetS_b_e_F) as BetS_F_e_F.
		pose proof (axiom_betweennessidentity F e) as n_BetS_F_e_F.
		contradict BetS_F_e_F.
		exact n_BetS_F_e_F.
	}


	assert (~ eq F e) as n_eq_F_e.
	{
		intro eq_F_e.
		
assert (Cong b F B E) as Cong_b_F_B_E by (rewrite eq_F_e; exact Cong_b_e_B_E).

		pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_C_b_D BetS_C_D_F) as BetS_b_D_F.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_b_D_F) as BetS_F_D_b.
		pose proof (cn_congruencereflexive F D) as Cong_F_D_F_D.
		pose proof (lemma_s_lt _ _ _ _ _ BetS_F_D_b Cong_F_D_F_D) as Lt_F_D_F_b.
		pose proof (cn_congruencereverse F b) as Cong_F_b_b_F.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_F_D_F_b Cong_F_b_b_F) as Lt_F_D_b_F.
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_B_E_D_F) as Cong_D_F_B_E.
		
		pose proof (lemma_congruenceflip D F B E Cong_D_F_B_E) as (_ & Cong_F_D_B_E & _).

		pose proof (lemma_lessthancongruence_smaller _ _ _ _ _ _ Lt_F_D_b_F Cong_F_D_B_E) as Lt_B_E_b_F.
		pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_b_F_B_E Cong_B_E_b_e) as Cong_b_F_b_e.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_B_E_b_F Cong_b_F_b_e) as Lt_B_E_b_e.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_B_E_b_F Cong_b_F_B_E) as Lt_B_E_B_E.
		pose proof (lemma_trichotomy_asymmetric _ _ _ _ Lt_B_E_B_E (* not real *)) as n_Lt_B_E_B_E.
		contradict Lt_B_E_B_E.
		exact n_Lt_B_E_B_E.
	}
	assert (neq_F_E := n_eq_F_e).


	assert (~ ~ BetS b e F) as n_n_BetS_b_e_F.
	{
		intro n_BetS_b_e_F.
		pose proof (lemma_outerconnectivity _ _ _ _ BetS_C_b_F BetS_C_b_e n_BetS_b_F_e n_BetS_b_e_F) as eq_F_e.
		contradict eq_F_e.
		exact n_eq_F_e.
	}

	assert (BetS_b_e_F := n_n_BetS_b_e_F).
	apply Classical_Prop.NNPP in BetS_b_e_F.
	pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_C_b_e BetS_b_e_F) as BetS_C_e_F.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_A_E_C_e) as Cong_C_e_A_E.
	pose proof (lemma_s_lt _ _ _ _ _ BetS_C_e_F Cong_C_e_A_E) as Lt_A_E_C_F.

	exact Lt_A_E_C_F.
Qed.

End Euclid.
