Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Square.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_flip.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_rotate.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_collinear.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_equaltoright.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_leg_change.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_PGrectangle.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_paste5.
Require Import ProofCheckingEuclid.lemma_rectanglerotate.
Require Import ProofCheckingEuclid.lemma_squaresequal.
Require Import ProofCheckingEuclid.proposition_08.
Require Import ProofCheckingEuclid.proposition_11B.
Require Import ProofCheckingEuclid.proposition_46.
Require Import ProofCheckingEuclid.proposition_47.
Require Import ProofCheckingEuclid.proposition_48A.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_48 :
	forall A B C D E F G H K L M,
	Triangle A B C ->
	Square A B F G ->
	Square A C K H ->
	Square B C E D ->
	BetS B M C ->
	BetS E L D ->
	EqAreaQuad A B F G B M L D ->
	EqAreaQuad A C K H M C E L ->
	Rectangle M C E L ->
	RightTriangle B A C.
Proof.
	intros A B C D E F G H K L M.
	intros Triangle_A_B_C.
	intros Square_A_B_F_G.
	intros Square_A_C_K_H.
	intros Square_B_C_E_D.
	intros BetS_B_M_C.
	intros BetS_E_L_D.
	intros EqAreaQuad_A_B_F_G_B_M_L_D.
	intros EqAreaQuad_A_C_K_H_M_C_E_L.
	intros Rectangle_M_C_E_L.

	pose proof (cn_congruencereflexive A B) as Cong_A_B_A_B.

	assert (eq B B) as eq_B_B by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C A B B eq_B_B) as Col_A_B_B.
	
	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_A_B_C) as nCol_A_B_C.
	
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).

	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_A_B_F_G_B_M_L_D) as EqAreaQuad_B_M_L_D_A_B_F_G.
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_A_C_K_H_M_C_E_L) as EqAreaQuad_M_C_E_L_A_C_K_H.

	pose proof (lemma_extension B A A B neq_B_A neq_A_B) as (R & BetS_B_A_R & _).
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_R) as BetS_R_A_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_A_R) as (neq_A_R & _ & neq_B_R).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_R_A_B) as (_ & neq_R_A & neq_R_B).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_A_R) as Col_B_A_R.
	pose proof (by_prop_Col_order _ _ _ Col_B_A_R) as (Col_A_B_R & Col_A_R_B & Col_R_B_A & Col_B_R_A & Col_R_A_B).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_B_C Col_A_B_R Col_A_B_B neq_R_B) as nCol_R_B_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_R_B_C) as (nCol_B_R_C & _ & _ & _ & _).

	pose proof (proposition_11B _ _ _ _ BetS_B_A_R nCol_B_R_C) as (Q & RightTriangle_B_A_Q & _).

	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_B_A_Q) as nCol_B_A_Q.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_A_Q) as (_ & neq_A_Q & _ & _ & _ & _).

	pose proof (lemma_layoff _ _ _ _ neq_A_Q neq_A_C) as (c & OnRay_A_Q_c & Cong_A_c_A_C).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_A_c_A_C) as Cong_A_C_A_c.

	pose proof (by_prop_RightTriangle_leg_change _ _ _ _ RightTriangle_B_A_Q OnRay_A_Q_c) as RightTriangle_B_A_c.
	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_B_A_c) as nCol_B_A_c.
	pose proof (by_prop_nCol_order _ _ _ nCol_B_A_c) as (nCol_A_B_c & nCol_A_c_B & nCol_c_B_A & nCol_B_c_A & nCol_c_A_B).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_A_c) as (_ & neq_A_c & neq_B_c & _ & neq_c_A & neq_c_B).

	pose proof (by_def_Triangle _ _ _ nCol_A_B_c) as Triangle_A_B_c.

	pose proof (proposition_46 _ _ _ neq_A_B nCol_A_B_c) as (f & g & Square_A_B_f_g & OppositeSide_g_A_B_c & _).

	pose proof (lemma_squaresequal _ _ _ _ _ _ _ _ Cong_A_B_A_B Square_A_B_F_G Square_A_B_f_g) as EqAreaQuad_A_B_F_G_A_B_f_g.

	pose proof (by_prop_OppositeSide_flip _ _ _ _ OppositeSide_g_A_B_c) as OppositeSide_g_B_A_c.

	pose proof (proposition_46 _ _ _ neq_A_c nCol_A_c_B) as (k & h & Square_A_c_k_h & OppositeSide_h_A_c_B & _).

	pose proof (lemma_squaresequal _ _ _ _ _ _ _ _ Cong_A_C_A_c Square_A_C_K_H Square_A_c_k_h) as EqAreaQuad_A_C_K_H_A_c_k_h.

	pose proof (by_prop_OppositeSide_flip _ _ _ _ OppositeSide_h_A_c_B) as OppositeSide_h_c_A_B.

	pose proof (proposition_46 _ _ _ neq_B_c nCol_B_c_A) as (e & d & Square_B_c_e_d & OppositeSide_d_B_c_A & _).

	assert (Square_B_c_e_d_2 := Square_B_c_e_d).
	destruct Square_B_c_e_d_2 as (_ & _ & _ & _ & RightTriangle_B_c_e & _ &_).

	pose proof (by_prop_OppositeSide_flip _ _ _ _ OppositeSide_d_B_c_A) as OppositeSide_d_c_B_A.

	pose proof (
		proposition_47
		_ _ _ _ _ _ _ _ _
		Triangle_A_B_c
		RightTriangle_B_A_c
		Square_A_B_f_g OppositeSide_g_B_A_c Square_A_c_k_h OppositeSide_h_c_A_B Square_B_c_e_d OppositeSide_d_c_B_A
	) as (
		m & l &
		_ & BetS_B_m_c &
		Parallelogram_m_c_e_l & BetS_d_l_e &
		EqAreaQuad_A_B_f_g_B_m_l_d & EqAreaQuad_A_c_k_h_m_c_e_l
	).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_m_c) as (neq_m_c & _ & _).
	pose proof (by_def_Col_from_BetS_A_B_C B m c BetS_B_m_c) as Col_B_m_c.
	pose proof (by_prop_Col_order _ _ _ Col_B_m_c) as (_ & _ & _ & Col_B_c_m & _).

	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_m_c_e_l) as Parallelogram_c_e_l_m.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_d_l_e) as BetS_e_l_d.

	pose proof (
		axiom_EqAreaQuad_transitive _ _ _ _ _ _ _ _ _ _ _ _ EqAreaQuad_A_B_F_G_A_B_f_g EqAreaQuad_A_B_f_g_B_m_l_d
	) as EqAreaQuad_A_B_F_G_B_m_l_d.
	pose proof (
		axiom_EqAreaQuad_transitive _ _ _ _ _ _ _ _ _ _ _ _ EqAreaQuad_B_M_L_D_A_B_F_G EqAreaQuad_A_B_F_G_B_m_l_d
	) as EqAreaQuad_B_M_L_D_B_m_l_d.
	pose proof (
		axiom_EqAreaQuad_transitive _ _ _ _ _ _ _ _ _ _ _ _ EqAreaQuad_M_C_E_L_A_C_K_H EqAreaQuad_A_C_K_H_A_c_k_h
	) as EqAreaQuad_M_C_E_L_A_c_k_h.
	pose proof (
		axiom_EqAreaQuad_transitive _ _ _ _ _ _ _ _ _ _ _ _ EqAreaQuad_M_C_E_L_A_c_k_h EqAreaQuad_A_c_k_h_m_c_e_l
	) as EqAreaQuad_M_C_E_L_m_c_e_l.
	

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_B_c_e Col_B_c_m neq_m_c) as RightTriangle_m_c_e.
	pose proof (lemma_PGrectangle _ _ _ _ Parallelogram_c_e_l_m RightTriangle_m_c_e) as Rectangle_c_e_l_m.
	pose proof (lemma_rectanglerotate _ _ _ _ Rectangle_c_e_l_m) as Rectangle_e_l_m_c.
	pose proof (lemma_rectanglerotate _ _ _ _ Rectangle_e_l_m_c) as Rectangle_l_m_c_e.
	pose proof (lemma_rectanglerotate _ _ _ _ Rectangle_l_m_c_e) as Rectangle_m_c_e_l.

	pose proof (
		lemma_paste5
		_ _ _ _ _ _ _ _ _ _ _ _
		EqAreaQuad_B_M_L_D_B_m_l_d
		EqAreaQuad_M_C_E_L_m_c_e_l
		BetS_B_M_C BetS_B_m_c BetS_E_L_D BetS_e_l_d Rectangle_M_C_E_L Rectangle_m_c_e_l
	) as EqAreaQuad_B_C_E_D_B_c_e_d.

	pose proof (proposition_48A _ _ _ _ _ _ _ _ Square_B_C_E_D Square_B_c_e_d EqAreaQuad_B_C_E_D_B_c_e_d) as Cong_B_C_B_c.

	epose proof (
		proposition_08
		A B C A B c
		Triangle_A_B_C Triangle_A_B_c Cong_A_B_A_B Cong_A_C_A_c Cong_B_C_B_c
	) as (CongA_B_A_C_B_A_c & _ & _).

	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_B_A_c CongA_B_A_C_B_A_c) as RightTriangle_B_A_C.

	exact RightTriangle_B_A_C.
Qed.

End Euclid.
