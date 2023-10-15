Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Midpoint.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_rotate.
Require Import ProofCheckingEuclid.by_prop_SameSide_flip.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_samesidecollinear.
Require Import ProofCheckingEuclid.proposition_10.
Require Import ProofCheckingEuclid.proposition_42B.
Require Import ProofCheckingEuclid.proposition_44A.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_44 :
	forall A B D J N R a b c,
	Triangle a b c ->
	nCol J D N ->
	nCol A B R ->
	exists X Y Z, Parallelogram A B X Y /\ CongA A B X J D N /\ EqAreaQuad a b Z c A B X Y /\ Midpoint b Z c /\ OppositeSide X A B R.
Proof.
	intros A B D J N R a b c.
	intros Triangle_abc.
	intros nCol_J_D_N.
	intros nCol_A_B_R.

	assert (eq B B) as eq_B_B by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C B A B eq_B_B) as Col_B_A_B.
	pose proof (by_def_Col_from_eq_B_C A B B eq_B_B) as Col_A_B_B.

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_abc) as nCol_a_b_c.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_a_b_c) as (_ & neq_b_c & _ & _ & _ & _).

	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_R) as (nCol_B_A_R & _ & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_R) as (neq_A_B & _ & _ & _ & _ & _).

	pose proof (proposition_10 _ _ neq_b_c) as (m & BetS_b_m_c & Cong_mb_mc).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_b_m_c) as BetS_c_m_b.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_b_m_c) as (neq_m_c & neq_b_m & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_c_m_b) as (neq_m_b & neq_c_m & neq_c_b).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_b_m_c) as Col_b_m_c.
	pose proof (by_prop_Col_order _ _ _ Col_b_m_c) as (Col_m_b_c & Col_m_c_b & Col_c_b_m & Col_b_c_m & Col_c_m_b).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_mb_mc) as (_ & Cong_bm_mc & _).
	pose proof (by_def_Midpoint _ _ _ BetS_b_m_c Cong_bm_mc) as Midpoint_b_m_c.

	pose proof (lemma_extension _ _ _ _ neq_A_B neq_m_c) as (E & BetS_A_B_E & Cong_BE_mc).

	pose proof (by_def_Col_from_eq_B_C E B B eq_B_B) as Col_E_B_B.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_E) as BetS_E_B_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_B_E) as (neq_B_E & _ & neq_A_E).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_B_A) as (neq_B_A & neq_E_B & neq_E_A).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_B_E) as Col_A_B_E.
	pose proof (by_prop_Col_order _ _ _ Col_A_B_E) as (Col_B_A_E & Col_B_E_A & Col_E_A_B & Col_A_E_B & Col_E_B_A).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_A_R Col_B_A_B Col_B_A_E neq_B_E) as nCol_B_E_R.
	pose proof (by_prop_nCol_order _ _ _ nCol_B_E_R) as (_ & _ & nCol_R_B_E & _ & _).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BE_mc) as Cong_mc_BE.

	pose proof (lemma_extension _ _ _ _ neq_E_B neq_b_m) as (Q & BetS_E_B_Q & Cong_BQ_bm).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_B_Q) as BetS_Q_B_E.

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_BQ_bm Cong_bm_mc) as Cong_BQ_mc.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_BQ_mc Cong_mc_BE) as Cong_BQ_BE.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BQ_BE) as (_ & Cong_QB_BE & _).
	pose proof (by_def_Midpoint _ _ _ BetS_Q_B_E Cong_QB_BE) as Midpoint_Q_B_E.

	pose proof (proposition_42B _ _ _ _ _ _ _ _ _ _ _ Triangle_abc Midpoint_b_m_c nCol_J_D_N Midpoint_Q_B_E Cong_BE_mc nCol_R_B_E) as (
		G & F & Parallelogram_G_B_E_F & EqAreaQuad_a_b_m_c_G_B_E_F & CongA_EBG_JDN & SameSide_R_G_BE
	).

	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_G_B_E_F) as Parallelogram_B_E_F_G.

	assert (Parallelogram_G_B_E_F_2 := Parallelogram_G_B_E_F).
	destruct Parallelogram_G_B_E_F_2 as (Par_GB_EF & Par_GF_BE).

	pose proof (by_prop_Par_NC _ _ _ _ Par_GB_EF) as (nCol_G_B_E & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_G_B_E) as (_ & _ & _ & _ & nCol_E_B_G).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_E_B_G Col_E_B_A Col_E_B_B neq_A_B) as nCol_A_B_G.

	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_R_G_BE Col_B_E_A neq_B_A) as SameSide_R_G_BA.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_R_G_BA) as SameSide_R_G_AB.

	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_a_b_m_c_G_B_E_F) as (EqAreaQuad_a_b_m_c_B_E_F_G & _ & _ & _ & _ & _ & _).

	pose proof (proposition_44A _ _ _ _ _ _ _ _ Parallelogram_B_E_F_G CongA_EBG_JDN BetS_A_B_E) as (
		M & L & Parallelogram_A_B_M_L & CongA_ABM_JDN & EqAreaQuad_B_E_F_G_L_M_B_A & BetS_G_B_M
	).

	pose proof (axiom_EqAreaQuad_transitive _ _ _ _ _ _ _ _ _ _ _ _ EqAreaQuad_a_b_m_c_B_E_F_G EqAreaQuad_B_E_F_G_L_M_B_A) as EqAreaQuad_a_b_m_c_L_M_B_A.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_a_b_m_c_L_M_B_A) as (_ & EqAreaQuad_a_b_m_c_A_B_M_L & _ & _ & _ & _ & _).

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_G_B_M Col_A_B_B nCol_A_B_G) as OppositeSide_G_AB_M.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_R_G_AB OppositeSide_G_AB_M) as OppositeSide_R_AB_M.
	pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_R_AB_M) as OppositeSide_M_AB_R.

	exists M, L, m.
	split.
	exact Parallelogram_A_B_M_L.
	split.
	exact CongA_ABM_JDN.
	split.
	exact EqAreaQuad_a_b_m_c_A_B_M_L.
	split.
	exact Midpoint_b_m_c .
	exact OppositeSide_M_AB_R.
Qed.

End Euclid.
