Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B .
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Cross.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_SameSide.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_OnRay_assert.
Require Import ProofCheckingEuclid.by_prop_OnRay_impliescollinear.
Require Import ProofCheckingEuclid.by_prop_OnRay_neq_A_C.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_SameSide_reflexive.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_sameside_onray_EFAC_BFG_EGAC.
Require Import ProofCheckingEuclid.lemma_samesidetransitive.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_07.
Require Import ProofCheckingEuclid.proposition_29B.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_Playfairhelper :
	forall A B C D E,
	Par A B C D ->
	Par A B C E ->
	Cross A D B C ->
	Cross A E B C ->
	Col C D E.
Proof.
	intros A B C D E.
	intros Par_A_B_C_D.
	intros Par_A_B_C_E.
	intros Cross_A_D_B_C.
	intros Cross_A_E_B_C.

	assert (eq C C) as eq_C_C by (reflexivity).
	pose proof (by_def_Col_from_eq_A_B C C B eq_C_C) as Col_C_C_B.
	pose proof (by_def_Col_from_eq_A_C C E C eq_C_C) as Col_C_E_C.
	pose proof (cn_congruencereflexive C B) as Cong_C_B_C_B.

	pose proof (by_prop_Par_flip _ _ _ _ Par_A_B_C_D) as (Par_B_A_C_D & Par_A_B_D_C & Par_B_A_D_C).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_A_B_C_D) as Par_C_D_A_B.
	pose proof (by_prop_Par_flip _ _ _ _ Par_C_D_A_B) as (Par_D_C_A_B & Par_C_D_B_A & Par_D_C_B_A).
	pose proof (by_prop_Par_NC _ _ _ _ Par_A_B_C_D) as (nCol_A_B_C & nCol_A_C_D & nCol_B_C_D & nCol_A_B_D).

	pose proof (by_prop_nCol_order _ _ _ nCol_B_C_D) as (nCol_C_B_D & nCol_C_D_B & nCol_D_B_C & nCol_B_D_C & nCol_D_C_B).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_C_D) as (neq_B_C & neq_C_D & neq_B_D & neq_C_B & neq_D_C & neq_D_B).

	pose proof (by_def_OnRay_from_neq_A_B C B neq_C_B) as OnRay_C_B_B.
	
	pose proof (by_prop_Par_flip _ _ _ _ Par_A_B_C_E) as (Par_B_A_C_E & Par_A_B_E_C & Par_B_A_E_C).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_A_B_C_E) as Par_C_E_A_B.
	pose proof (by_prop_Par_flip _ _ _ _ Par_C_E_A_B) as (Par_E_C_A_B & Par_C_E_B_A & Par_E_C_B_A).
	pose proof (by_prop_Par_NC _ _ _ _ Par_A_B_C_E) as (_ & nCol_A_C_E & nCol_B_C_E & nCol_A_B_E).
	
	pose proof (by_prop_nCol_order _ _ _ nCol_B_C_E) as (nCol_C_B_E & nCol_C_E_B & nCol_E_B_C & nCol_B_E_C & nCol_E_C_B).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_C_E) as (_ & neq_C_E & neq_B_E & _ & neq_E_C & neq_E_B).

	pose proof (by_prop_CongA_reflexive _ _ _ nCol_E_C_B) as CongA_E_C_B_E_C_B.

	destruct Cross_A_D_B_C as (M & BetS_A_M_D & BetS_B_M_C).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_M_D) as BetS_D_M_A.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_C) as BetS_C_M_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_M_C) as (neq_M_C & neq_B_M & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_M_B) as (neq_M_B & neq_C_M & _).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_M_C) as Col_B_M_C.
	pose proof (by_prop_Col_order _ _ _ Col_B_M_C) as (Col_M_B_C & Col_M_C_B & Col_C_B_M & Col_B_C_M & Col_C_M_B).

	destruct Cross_A_E_B_C as (m & BetS_A_m_E & BetS_B_m_C).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_m_E) as BetS_E_m_A.
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_m_C) as BetS_C_m_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_m_C) as (neq_m_C & neq_B_m &_ ).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_m_B) as (neq_m_B & neq_C_m &_ ).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_m_C) as Col_B_m_C.
	pose proof (by_prop_Col_order _ _ _ Col_B_m_C) as (Col_m_B_C & Col_m_C_B & Col_C_B_m & Col_B_C_m & Col_C_m_B).

	pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_C_B_m Col_C_B_M BetS_E_m_A BetS_D_M_A nCol_C_B_E nCol_C_B_D) as SameSide_E_D_C_B.

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_E_m_A Col_C_B_m nCol_C_B_E) as OppositeSide_E_C_B_A.
	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_D_M_A Col_C_B_M nCol_C_B_D) as OppositeSide_D_C_B_A.

	pose proof (proposition_29B _ _ _ _ Par_E_C_B_A OppositeSide_E_C_B_A) as CongA_E_C_B_C_B_A.
	pose proof (proposition_29B _ _ _ _ Par_D_C_B_A OppositeSide_D_C_B_A) as CongA_D_C_B_C_B_A.

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_D_C_B_C_B_A) as CongA_C_B_A_D_C_B.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_E_C_B_C_B_A CongA_C_B_A_D_C_B) as CongA_E_C_B_D_C_B.

	pose proof (lemma_layoff _ _ _ _ neq_C_E neq_C_D) as (e & OnRay_C_E_e & Cong_C_e_C_D).

	pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_C_E_e) as Col_C_E_e.
	pose proof (by_prop_OnRay_neq_A_C _ _ _ OnRay_C_E_e) as neq_C_e.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_C_E_e) as OnRay_C_e_E.

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_C_e_C_D) as (Cong_e_C_D_C & _ & _).

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_E_C_B_E_C_B OnRay_C_E_e OnRay_C_B_B) as CongA_E_C_B_e_C_B.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_E_C_B_e_C_B) as CongA_e_C_B_E_C_B.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_e_C_B_E_C_B CongA_E_C_B_D_C_B) as CongA_e_C_B_D_C_B.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_C_E_B Col_C_E_C Col_C_E_e neq_C_e) as nCol_C_e_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_C_e_B) as (nCol_e_C_B & _ & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_e_C_B) as (_ & nCol_C_B_e & _ & _ & _).
	pose proof (by_def_Triangle _ _ _ nCol_e_C_B) as Triangle_e_C_B.
	pose proof (by_def_Triangle _ _ _ nCol_D_C_B) as Triangle_D_C_B.

	pose proof (by_prop_SameSide_reflexive _ _ _ nCol_C_B_e) as SameSide_e_e_C_B.

	pose proof (proposition_04 _ _ _ _ _ _ Cong_C_e_C_D Cong_C_B_C_B CongA_e_C_B_D_C_B) as (Cong_e_B_D_B & _ & _).

	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_e_e_C_B Col_C_C_B OnRay_C_e_E) as SameSide_e_E_C_B.
	pose proof (lemma_samesidetransitive _ _ _ _ _ SameSide_e_E_C_B SameSide_E_D_C_B) as SameSide_e_D_C_B.
	pose proof (proposition_07 _ _ _ _ neq_C_B Cong_e_C_D_C Cong_e_B_D_B SameSide_e_D_C_B) as eq_e_D.

	assert (Col C E D) as Col_C_E_D by (rewrite <- eq_e_D; exact Col_C_E_e).
	pose proof (by_prop_Col_order _ _ _ Col_C_E_D) as (_ & _ & _ & Col_C_D_E & _).

	exact Col_C_D_E.
Qed.

End Euclid.
