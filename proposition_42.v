Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E .
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B .
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B .
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_Supp.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_flip.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_OnRay_impliescollinear.
Require Import ProofCheckingEuclid.by_prop_OnRay_neq_A_C.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_flip.
Require Import ProofCheckingEuclid.by_prop_Parallelogram_rotate.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_angletrichotomy_n_CongA_ABC_DEF_n_LtA_DEF_ABC_LtA_ABC_DEF .
Require Import ProofCheckingEuclid.lemma_crossbar_LtA.
Require Import ProofCheckingEuclid.lemma_diagonalsmeet.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_sameside_onray_EFAC_BFG_EGAC.
Require Import ProofCheckingEuclid.lemma_samesidecollinear.
Require Import ProofCheckingEuclid.lemma_supplementinequality.
Require Import ProofCheckingEuclid.lemma_triangletoparallelogram.
Require Import ProofCheckingEuclid.proposition_07.
Require Import ProofCheckingEuclid.proposition_23C.
Require Import ProofCheckingEuclid.proposition_31.
Require Import ProofCheckingEuclid.proposition_34.
Require Import ProofCheckingEuclid.proposition_38.
Require Import ProofCheckingEuclid.proposition_41.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_42 :
	forall A B C D E J K,
	Triangle A B C ->
	nCol J D K ->
	Midpoint B E C ->
	exists X Z, Parallelogram X E C Z /\ EqAreaQuad A B E C X E C Z /\ CongA C E X J D K /\ Col X Z A.
Proof.
	intros A B C D E J K.
	intros Triangle_A_B_C.
	intros nCol_J_D_K.
	intros Midpoint_B_E_C.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq E E) as eq_E_E by (reflexivity).

	pose proof (by_def_Col_from_eq_A_C B C B eq_B_B) as Col_B_C_B.
	pose proof (by_def_Col_from_eq_A_C E B E eq_E_E) as Col_E_B_E.
	pose proof (by_def_Col_from_eq_A_C E C E eq_E_E) as Col_E_C_E.
	pose proof (by_def_Col_from_eq_B_C A E E eq_E_E) as Col_A_E_E.
	pose proof (by_def_Col_from_eq_B_C B C C eq_C_C) as Col_B_C_C.
	pose proof (by_def_Col_from_eq_B_C B E E eq_E_E) as Col_B_E_E.

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_A_B_C) as nCol_A_B_C.
	
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).

	pose proof (by_prop_nCol_order _ _ _ nCol_J_D_K) as (nCol_D_J_K & nCol_D_K_J & nCol_K_J_D & nCol_J_K_D & nCol_K_D_J).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_J_D_K) as (neq_J_D & neq_D_K & neq_J_K & neq_D_J & neq_K_D & neq_K_J).

	destruct Midpoint_B_E_C as (BetS_B_E_C & Cong_B_E_E_C).
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_E_C) as BetS_C_E_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_E_C) as (neq_E_C & neq_B_E & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_E_B) as (neq_E_B & neq_C_E & _).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_E_C) as Col_B_E_C.
	pose proof (by_prop_Col_order _ _ _ Col_B_E_C) as (Col_E_B_C & Col_E_C_B & Col_C_B_E & Col_B_C_E & Col_C_E_B).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_B_E_E_C) as (Cong_E_B_C_E & Cong_E_B_E_C & Cong_B_E_C_E).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_B_E_E_C) as Cong_E_C_B_E.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_E_C_B_E) as (Cong_C_E_E_B & Cong_C_E_B_E & Cong_E_C_E_B).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_C_A Col_B_C_E Col_B_C_C neq_E_C) as nCol_E_C_A.

	pose proof (proposition_23C _ _ _ _ _ _ neq_E_C nCol_J_D_K nCol_E_C_A) as (f & c & OnRay_E_C_c & CongA_f_E_c_J_D_K & SameSide_f_A_E_C).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_f_A_E_C) as (SameSide_A_f_E_C & _ & _).

	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_A_f_E_C Col_E_C_B neq_E_B) as SameSide_A_f_E_B.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_A_f_E_B) as (SameSide_f_A_E_B & _ & _).
	
	assert (SameSide_A_f_E_B_2 := SameSide_A_f_E_B).
	destruct SameSide_A_f_E_B_2 as (_ & _ & _ & _ & _ & _ & _ & nCol_E_B_A & nCol_E_B_f).
	
	pose proof (by_prop_nCol_order _ _ _ nCol_E_B_f) as (nCol_B_E_f & nCol_B_f_E & nCol_f_E_B & nCol_E_f_B & nCol_f_B_E).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_E_B_f) as (_ & neq_B_f & neq_E_f & _ & neq_f_B & neq_f_E).
	
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_E_B_f Col_E_B_E Col_E_B_C neq_E_C) as nCol_E_C_f.
	pose proof (by_prop_nCol_order _ _ _ nCol_E_C_f) as (nCol_C_E_f & _ & _ & _ & _).

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_E_f) as CongA_B_E_f_f_E_B.

	pose proof (proposition_31 _ _ _ _ BetS_B_E_C nCol_B_C_A) as (
		P & Q & M &
		BetS_P_A_Q &
		CongA_Q_A_E_A_E_B & CongA_Q_A_E_B_E_A & CongA_E_A_Q_B_E_A &
		CongA_P_A_E_A_E_C & CongA_P_A_E_C_E_A & CongA_E_A_P_C_E_A &
		Par_P_Q_B_C &
		Cong_P_A_E_C & Cong_A_Q_B_E & Cong_A_M_M_E &
		Cong_P_M_M_C & Cong_B_M_M_Q &
		BetS_P_M_C & BetS_B_M_Q & BetS_A_M_E
	).

	pose proof (by_def_Col_from_eq_B_C P A A eq_A_A) as Col_P_A_A.
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_A_Q) as BetS_Q_A_P.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_P_A_Q) as (neq_A_Q & neq_P_A & neq_P_Q).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_Q_A_P) as (neq_A_P & neq_Q_A & neq_Q_P).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_P_A_Q) as Col_P_A_Q.
	pose proof (by_prop_Col_order _ _ _ Col_P_A_Q) as (Col_A_P_Q & Col_A_Q_P & Col_Q_P_A & Col_P_Q_A & Col_Q_A_P).

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_P_A_E_A_E_C) as CongA_A_E_C_P_A_E.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_A_E_C_P_A_E) as nCol_P_A_E.
	
	pose proof (by_prop_nCol_order _ _ _ nCol_P_A_E) as (nCol_A_P_E & nCol_A_E_P & nCol_E_P_A & nCol_P_E_A & nCol_E_A_P).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_P_A_E) as (_ & neq_A_E & neq_P_E & _ & neq_E_A & neq_E_P).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_C_A Col_B_C_B Col_B_C_E neq_B_E) as nCol_B_E_A.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_E_A) as CongA_B_E_A_A_E_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_B_E_A) as (_ & _ & _ & _ & nCol_A_E_B).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_C_A Col_B_C_C Col_B_C_E neq_C_E) as nCol_C_E_A.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_P_A_E Col_P_A_Q Col_P_A_A neq_Q_A) as nCol_Q_A_E.
	pose proof (by_prop_nCol_order _ _ _ nCol_Q_A_E) as (_ & _ & _ & _ & nCol_E_A_Q).
	
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_A_M_M_E) as (Cong_M_A_E_M & Cong_M_A_M_E & Cong_A_M_E_M).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_A_M_M_E) as Cong_M_E_A_M.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_M_E_A_M) as (Cong_E_M_M_A & Cong_E_M_A_M & Cong_M_E_M_A).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_P_M_M_C) as Cong_M_C_P_M.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_M_C_P_M) as (_ & _ & Cong_M_C_M_P).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_B_M_M_Q) as (_ & Cong_M_B_M_Q & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_M_C) as BetS_C_M_P.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_M_E) as BetS_E_M_A.

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_P_Q_B_C Col_B_C_E neq_E_C) as Par_P_Q_E_C.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_P_Q_E_C) as Par_E_C_P_Q.
	pose proof (by_prop_Par_flip _ _ _ _ Par_P_Q_B_C) as (_ & Par_P_Q_C_B & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_P_Q_C_B Col_C_B_E neq_E_B) as Par_P_Q_E_B.
	pose proof (by_prop_Par_flip _ _ _ _ Par_P_Q_E_B) as (_ & Par_P_Q_B_E & _).
	
	assert (Par_P_Q_E_C_2 := Par_P_Q_E_C).
	destruct Par_P_Q_E_C_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_P_Q_E_C & _ & _).

	pose proof (by_def_OnRay_from_neq_A_B E C neq_E_C) as OnRay_E_C_C.
	pose proof (by_def_OnRay_from_neq_A_B E A neq_E_A) as OnRay_E_A_A.
	pose proof (by_def_OnRay_from_neq_A_B E f neq_E_f) as OnRay_E_f_f.
	pose proof (by_def_OnRay_from_neq_A_B E B neq_E_B) as OnRay_E_B_B.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_E_A_A BetS_C_E_B) as Supp_C_E_A_A_B.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_E_f_f BetS_C_E_B) as Supp_C_E_f_f_B.

	assert (~ ~ Meet E f P Q) as n_n_Meet_E_f_P_Q.
	{
		intro n_Meet_E_f_P_Q.

		assert (~ LtA C E f C E A) as n_LtA_C_E_f_C_E_A.
		{
			intro LtA_C_E_f_C_E_A.

			pose proof (lemma_crossbar_LtA _ _ _ _ _ _ LtA_C_E_f_C_E_A SameSide_f_A_E_C OnRay_E_C_C OnRay_E_A_A) as (m & BetS_A_m_C & OnRay_E_f_m).

			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_m_C) as BetS_C_m_A.

			pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_E_f_m) as Col_E_f_m.
			pose proof (by_prop_Col_order _ _ _ Col_E_f_m) as (_ & _ & Col_m_E_f & _ & _).

			pose proof (postulate_Euclid5 _ _ _ _ _ _ BetS_C_M_P BetS_E_M_A BetS_C_m_A Cong_E_M_A_M Cong_M_C_M_P nCol_E_A_P) as (F & BetS_E_m_F & BetS_P_A_F).
			
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_m_F) as BetS_F_m_E.
			pose proof (by_prop_BetS_notequal _ _ _ BetS_E_m_F) as (neq_m_F & neq_E_m & neq_E_F).
			pose proof (by_prop_BetS_notequal _ _ _ BetS_F_m_E) as (neq_m_E & neq_F_m & neq_F_E).
			pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_m_F) as Col_E_m_F.
			pose proof (by_prop_Col_order _ _ _ Col_E_m_F) as (Col_m_E_F & Col_m_F_E & Col_F_E_m & Col_E_F_m & Col_F_m_E).

			pose proof (by_def_Col_from_BetS_A_B_C P A F BetS_P_A_F) as Col_P_A_F.
			pose proof (by_prop_Col_order _ _ _ Col_P_A_F) as (Col_A_P_F & _ & _ & _ & _).

			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_m_E_f Col_m_E_F neq_m_E) as Col_E_f_F.
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_P_F Col_A_P_Q neq_A_P) as Col_P_F_Q.
			pose proof (by_prop_Col_order _ _ _ Col_P_F_Q) as (_ & _ & _ & Col_P_Q_F & _).
			pose proof (by_def_Meet _ _ _ _ _ neq_E_f neq_P_Q Col_E_f_F Col_P_Q_F) as Meet_E_f_P_Q.

			contradict Meet_E_f_P_Q.
			exact n_Meet_E_f_P_Q.
		}


		assert (~ LtA C E A C E f) as n_LtA_C_E_A_C_E_f.
		{
			intro LtA_C_E_A_C_E_f.

			pose proof (lemma_supplementinequality _ _ _ _ _ _ _ _ _ _ Supp_C_E_f_f_B Supp_C_E_A_A_B LtA_C_E_A_C_E_f) as LtA_f_E_B_A_E_B.
			pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_f_E_B_A_E_B CongA_B_E_f_f_E_B) as LtA_B_E_f_A_E_B.
			pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_B_E_f_A_E_B CongA_B_E_A_A_E_B) as LtA_B_E_f_B_E_A.

			pose proof (lemma_crossbar_LtA _ _ _ _ _ _ LtA_B_E_f_B_E_A SameSide_f_A_E_B OnRay_E_B_B OnRay_E_A_A) as (m & BetS_A_m_B & OnRay_E_f_m).

			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_m_B) as BetS_B_m_A.

			pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_E_f_m) as Col_E_f_m.
			pose proof (by_prop_Col_order _ _ _ Col_E_f_m) as (_ & _ & Col_m_E_f & _ & _).

			pose proof (postulate_Euclid5 _ _ _ _ _ _ BetS_B_M_Q BetS_E_M_A BetS_B_m_A Cong_E_M_A_M Cong_M_B_M_Q nCol_E_A_Q) as (F & BetS_E_m_F & BetS_Q_A_F).

			pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_m_F) as BetS_F_m_E.
			pose proof (by_prop_BetS_notequal _ _ _ BetS_E_m_F) as (neq_m_F & neq_E_m & neq_E_F).
			pose proof (by_prop_BetS_notequal _ _ _ BetS_F_m_E) as (neq_m_E & neq_F_m & neq_F_E).
			pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_m_F) as Col_E_m_F.
			pose proof (by_prop_Col_order _ _ _ Col_E_m_F) as (Col_m_E_F & Col_m_F_E & Col_F_E_m & Col_E_F_m & Col_F_m_E).

			pose proof (by_def_Col_from_BetS_A_B_C Q A F BetS_Q_A_F) as Col_Q_A_F.
			pose proof (by_prop_Col_order _ _ _ Col_Q_A_F) as (Col_A_Q_F & _ & _ & _ & _).

			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_m_E_f Col_m_E_F neq_m_E) as Col_E_f_F.
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_Q_F Col_A_Q_P neq_A_Q) as Col_Q_F_P.
			pose proof (by_prop_Col_order _ _ _ Col_Q_F_P) as (_ & _ & Col_P_Q_F & _ & _).
			pose proof (by_def_Meet _ _ _ _ _ neq_E_f neq_P_Q Col_E_f_F Col_P_Q_F) as Meet_E_f_P_Q.

			contradict Meet_E_f_P_Q.
			exact n_Meet_E_f_P_Q.
		}


		assert (~ ~ CongA C E A C E f) as n_n_CongA_C_E_A_C_E_f.
		{
			intro n_CongA_C_E_A_C_E_f.

			pose proof (lemma_angletrichotomy_n_CongA_ABC_DEF_n_LtA_DEF_ABC_LtA_ABC_DEF _ _ _ _ _ _ nCol_C_E_A nCol_C_E_f n_CongA_C_E_A_C_E_f n_LtA_C_E_f_C_E_A) as LtA_C_E_A_C_E_f.

			contradict LtA_C_E_A_C_E_f.
			exact n_LtA_C_E_A_C_E_f.
		}
		assert (CongA_C_E_A_C_E_f := n_n_CongA_C_E_A_C_E_f).
		apply Classical_Prop.NNPP in CongA_C_E_A_C_E_f.

		pose proof (CongA_C_E_A_C_E_f) as (d & a & p & q & OnRay_E_C_d & OnRay_E_A_a & OnRay_E_C_p & OnRay_E_f_q & Cong_E_d_E_p & Cong_E_a_E_q & Cong_d_a_p_q & _).

		pose proof (by_def_Col_from_eq_A_C E d E eq_E_E) as Col_E_d_E.
		pose proof (by_prop_Col_order _ _ _ Col_E_d_E) as (_ & _ & Col_E_E_d & _ & _).

		pose proof (lemma_layoffunique _ _ _ _ OnRay_E_C_d OnRay_E_C_p Cong_E_d_E_p) as eq_d_p.

		pose proof (by_prop_OnRay_neq_A_C _ _ _ OnRay_E_C_d) as neq_E_d.
		pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_E_C_d) as Col_E_C_d.

		pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_E_A_a) as Col_E_A_a.
		pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_E_f_q) as Col_E_f_q.
		pose proof (by_prop_Col_order _ _ _ Col_E_f_q) as (_ & _ & Col_q_E_f & _ & _).

		pose proof (by_prop_OnRay_neq_A_C _ _ _ OnRay_E_f_q) as neq_E_q.
		pose proof (by_prop_neq_symmetric _ _ neq_E_q) as neq_q_E.

		pose proof (by_prop_Cong_flip _ _ _ _ Cong_E_a_E_q) as (Cong_a_E_q_E & _ & _).

		pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_A_f_E_C Col_E_C_d neq_E_d) as SameSide_A_f_E_d.
		pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_A_f_E_d Col_E_E_d OnRay_E_f_q) as SameSide_A_q_E_d.
		pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_A_q_E_d) as (SameSide_q_A_E_d & _ & _).
		pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_q_A_E_d Col_E_E_d OnRay_E_A_a) as SameSide_q_a_E_d.
		pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_q_a_E_d) as (SameSide_a_q_E_d & _ & _).

		assert (Cong d a d q) as Cong_d_a_d_q by (setoid_rewrite eq_d_p at 2; exact Cong_d_a_p_q).
		pose proof (by_prop_Cong_flip _ _ _ _ Cong_d_a_d_q) as (Cong_a_d_q_d & _ & _).

		pose proof (proposition_07 _ _ _ _ neq_E_d Cong_a_E_q_E Cong_a_d_q_d SameSide_a_q_E_d) as eq_a_q.
		assert (Col E A q) as Col_E_A_q by (rewrite <- eq_a_q; exact Col_E_A_a).

		pose proof (by_prop_Col_order _ _ _ Col_E_A_q) as (_ & _ & Col_q_E_A & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_q_E_A Col_q_E_f neq_q_E) as Col_E_A_f.
		pose proof (by_prop_Col_order _ _ _ Col_E_A_f) as (_ & _ & _ & Col_E_f_A & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_E_f neq_P_Q Col_E_f_A Col_P_Q_A) as Meet_E_f_P_Q.

		contradict Meet_E_f_P_Q.
		exact n_Meet_E_f_P_Q.
	}
	assert (Meet_E_f_P_Q := n_n_Meet_E_f_P_Q).
	apply Classical_Prop.NNPP in Meet_E_f_P_Q.


	destruct Meet_E_f_P_Q as (F & _ & _ & Col_E_f_F & Col_P_Q_F).

	pose proof (by_prop_Col_order _ _ _ Col_P_Q_F) as (Col_Q_P_F & _ & _ & _ & _).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_Q_P_A Col_Q_P_F neq_Q_P) as Col_P_A_F.
	pose proof (by_prop_Col_order _ _ _ Col_P_A_F) as (_ & Col_A_F_P & _ & _ & _).

	pose proof (lemma_triangletoparallelogram _ _ _ _ _ Par_E_C_P_Q Col_P_Q_F) as (G & Parallelogram_F_G_C_E & Col_P_Q_G).

	pose proof (by_prop_Parallelogram_flip _ _ _ _ Parallelogram_F_G_C_E) as Parallelogram_G_F_E_C.
	pose proof (by_prop_Parallelogram_rotate _ _ _ _ Parallelogram_G_F_E_C) as Parallelogram_F_E_C_G.
	pose proof (by_prop_Parallelogram_flip _ _ _ _ Parallelogram_F_E_C_G) as Parallelogram_E_F_G_C.

	pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_P_Q Col_P_Q_F Col_P_Q_G Col_P_Q_A) as Col_F_G_A.

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_P_Q_A Col_P_Q_F neq_P_Q) as Col_Q_A_F.
	pose proof (by_prop_Col_order _ _ _ Col_Q_A_F) as (_ & Col_A_F_Q & _ & _ & _).
	
	assert (Parallelogram_F_E_C_G_2 := Parallelogram_F_E_C_G).
	destruct Parallelogram_F_E_C_G_2 as (Par_F_E_C_G & Par_F_G_E_C).

	pose proof (by_prop_Par_NC _ _ _ _ Par_F_E_C_G) as (_ & _ & _ & nCol_F_E_G).
	pose proof (by_prop_Par_NC _ _ _ _ Par_F_E_C_G) as (nCol_F_E_C & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_F_E_C) as (_ & _ & _ & nCol_F_C_E & _).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_F_E_G) as (_ & _ & neq_F_G & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_F_E_G) as (neq_F_E & _ & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_F_E) as neq_E_F.

	pose proof (by_prop_nCol_order _ _ _ nCol_F_C_E) as (_ & nCol_C_E_F & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_C_E_F) as (nCol_E_C_F & _ & _ & _ & _).
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_C_E_F) as CongA_C_E_F_C_E_F.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_C_E_F) as CongA_C_E_F_F_E_C.

	pose proof (proposition_38 _ _ _ _ _ _ _ _ Par_P_Q_B_E Col_P_Q_A Col_P_Q_A Cong_B_E_E_C Col_B_E_E Col_B_E_C) as EqAreaTri_A_B_E_A_E_C.
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_A_B_E_A_E_C) as EqAreaTri_A_E_C_A_B_E.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_A_E_C_A_B_E) as (_ & EqAreaTri_A_E_C_A_E_B & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_A_E_C_A_E_B) as EqAreaTri_A_E_B_A_E_C.

	pose proof (proposition_34 _ _ _ _ Parallelogram_E_F_G_C) as (_ & _ & _ & _ & CongTriangles_F_E_C_C_G_F).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_F_E_C_C_G_F) as EqAreaTri_F_E_C_C_G_F.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_F_E_C_C_G_F) as (_ & _ & _ & _ & EqAreaTri_F_E_C_F_C_G).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_F_E_C_F_C_G) as EqAreaTri_F_C_G_F_E_C.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_F_C_G_F_E_C) as (_ & EqAreaTri_F_C_G_F_C_E & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_F_C_G_F_C_E) as EqAreaTri_F_C_E_F_C_G.

	pose proof (proposition_41 _ _ _ _ _ Parallelogram_F_E_C_G Col_F_G_A) as EqAreaTri_F_E_C_A_E_C.
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_F_E_C_A_E_C) as EqAreaTri_A_E_C_F_E_C.
	pose proof (axiom_EqAreaTri_transitive _ _ _ _ _ _ _ _ _ EqAreaTri_A_E_B_A_E_C EqAreaTri_A_E_C_F_E_C) as EqAreaTri_A_E_B_F_E_C.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_A_E_B_F_E_C) as (_ & EqAreaTri_A_E_B_F_C_E & _ & _ & _).
	pose proof (axiom_EqAreaTri_transitive _ _ _ _ _ _ _ _ _ EqAreaTri_A_E_C_F_E_C EqAreaTri_F_E_C_F_C_G) as EqAreaTri_A_E_C_F_C_G.

	pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_E_F_G_C) as (m & BetS_E_m_G & BetS_F_m_C).

	assert (BetS A E E \/ eq A E \/ eq E E) as eq_E_E' by (right; right; exact eq_E_E).
	assert (BetS F m C \/ eq F m \/ eq m C) as BetS_F_m_C' by (left; exact BetS_F_m_C).

	epose proof (
		axiom_paste3
		A E B C E F C E G m
		EqAreaTri_A_E_B_F_C_E
		EqAreaTri_A_E_C_F_C_G
		BetS_B_E_C
		eq_E_E'
		BetS_E_m_G
		BetS_F_m_C'
	) as EqAreaQuad_A_B_E_C_F_E_C_G.


	(* assert by cases *)
	assert (OnRay E F f) as OnRay_E_F_f.
	assert (Col_E_f_F_2 := Col_E_f_F).
	destruct Col_E_f_F_2 as [eq_E_f | [eq_E_F | [eq_f_F | [BetS_f_E_F | [BetS_E_f_F | BetS_E_F_f]]]]].
	{
		(* case eq_E_f *)
		contradict eq_E_f.
		exact neq_E_f.
	}
	{
		(* case eq_E_F *)
		contradict eq_E_F.
		exact neq_E_F.
	}
	{
		(* case eq_f_F *)
		pose proof (by_def_OnRay_from_neq_A_B E F neq_E_F) as OnRay_E_F_F.
		assert (OnRay E F f) as OnRay_E_F_f by (rewrite eq_f_F; exact OnRay_E_F_F).

		exact OnRay_E_F_f.
	}
	{
		(* case BetS_f_E_F *)

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_f_E_F) as BetS_F_E_f.
		pose proof (by_def_OppositeSide _ _ _ _ _ BetS_F_E_f Col_E_C_E nCol_E_C_F) as OppositeSide_F_E_C_f.
		pose proof (by_prop_OppositeSide_symmetric _ _ _ _ OppositeSide_F_E_C_f) as OppositeSide_f_E_C_F.
		pose proof (lemma_planeseparation _ _ _ _ _ SameSide_A_f_E_C OppositeSide_f_E_C_F) as OppositeSide_A_E_C_F.

		destruct OppositeSide_A_E_C_F as (j & BetS_A_j_F & Col_E_C_j & _).

		pose proof (by_prop_BetS_notequal _ _ _ BetS_A_j_F) as (_ & _ & neq_A_F).
		pose proof (by_def_Col_from_BetS_A_B_C A j F BetS_A_j_F) as Col_A_j_F.
		pose proof (by_prop_Col_order _ _ _ Col_A_j_F) as (_ & _ & _ & Col_A_F_j & _).

		pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_A_F Col_A_F_P Col_A_F_Q Col_A_F_j) as Col_P_Q_j.
		pose proof (by_def_Meet _ _ _ _ _ neq_P_Q neq_E_C Col_P_Q_j Col_E_C_j) as Meet_P_Q_E_C.

		contradict Meet_P_Q_E_C.
		exact n_Meet_P_Q_E_C.
	}
	{
		(* case BetS_E_f_F *)
		pose proof (by_def_OnRay_from_BetS_A_E_B E F f BetS_E_f_F neq_E_F) as OnRay_E_F_f.

		exact OnRay_E_F_f.
	}
	{
		(* case BetS_E_F_f *)
		pose proof (by_def_OnRay_from_BetS_A_B_E E F f BetS_E_F_f neq_E_F) as OnRay_E_F_f.

		exact OnRay_E_F_f.
	}

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_C_E_F_C_E_F OnRay_E_C_c OnRay_E_F_f) as CongA_C_E_F_c_E_f.
	pose proof (by_prop_CongA_flip _ _ _ _ _ _ CongA_C_E_F_c_E_f) as CongA_F_E_C_f_E_c.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_F_E_C_f_E_c CongA_f_E_c_J_D_K) as CongA_F_E_C_J_D_K.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_C_E_F_F_E_C CongA_F_E_C_J_D_K) as CongA_C_E_F_J_D_K.

	exists F, G.
	split.
	exact Parallelogram_F_E_C_G.
	split.
	exact EqAreaQuad_A_B_E_C_F_E_C_G.
	split.
	exact CongA_C_E_F_J_D_K .
	exact Col_F_G_A.
Qed.

End Euclid.
