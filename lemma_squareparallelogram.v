Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_OnRay.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_flip.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_collinear.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Euclid4.
Require Import ProofCheckingEuclid.lemma_betweennesspreserved.
Require Import ProofCheckingEuclid.lemma_diagonalsbisect.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_righttogether.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_46.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

(* Can't use lemma_twoperpsparallel since SameSide needs to be proven first. *)
Lemma lemma_squareparallelogram :
	forall A B C D,
	Square A B C D ->
	Parallelogram A B C D.
Proof.
	intros A B C D.
	intros Square_A_B_C_D.

	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C D A A eq_A_A) as Col_D_A_A.

	pose proof (cn_congruencereflexive D A) as Cong_DA_DA.

	destruct Square_A_B_C_D as (
		Cong_AB_CD & Cong_AB_BC & Cong_AB_DA & RightTriangle_DAB & RightTriangle_ABC & RightTriangle_BCD & RightTriangle_CDA
	).

	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_DAB) as nCol_D_A_B.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_D_A_B) as (neq_D_A & _ & _ & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_D_A_B) as (_ & neq_A_B & _ & _ & _ & _).

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_CDA) as RightTriangle_ADC.
	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_CDA) as nCol_C_D_A.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_C_D_A) as (_ & _ & _ & neq_D_C & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_D_C) as OnRay_DC_C.

	pose proof (lemma_extension _ _ _ _ neq_D_A neq_D_A) as (R & BetS_D_A_R & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_A_R) as BetS_R_A_D.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_D_A_R) as (neq_A_R & _ & neq_D_R).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_R_A_D) as (neq_A_D & neq_R_A & neq_R_D).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_D_A_R) as Col_D_A_R.
	pose proof (by_prop_Col_order _ _ _ Col_D_A_R) as (Col_A_D_R & Col_A_R_D & Col_R_D_A & Col_D_R_A & Col_R_A_D).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_D_A_B Col_D_A_R Col_D_A_A neq_R_A) as nCol_R_A_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_R_A_B) as (_ & nCol_A_B_R & _ & _ & _).

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_DAB Col_D_A_R neq_R_A) as RightTriangle_RAB.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_RAB) as RightTriangle_BAR.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_A_D) as OnRay_AD_D.

	pose proof (proposition_46 _ _ _ neq_A_B nCol_A_B_R) as (c & E & Square_A_B_c_E & OppositeSide_E_AB_R & Parallelogram_A_B_c_E).

	assert (Square_A_B_c_E_2 := Square_A_B_c_E).
	destruct Square_A_B_c_E_2 as (
		Cong_AB_cE & Cong_AB_Bc & Cong_AB_EA & RightTriangle_EAB & RightTriangle_ABc & RightTriangle_BcE & RightTriangle_cEA
	).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AB_Bc) as Cong_Bc_AB.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_Bc_AB Cong_AB_BC) as Cong_Bc_BC.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_Bc_BC) as (Cong_cB_CB & _ & _).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AB_EA) as Cong_EA_AB.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_EA_AB Cong_AB_DA) as Cong_EA_DA.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_EA_DA) as (Cong_AE_AD & _ & _).

	pose proof (by_prop_OppositeSide_flip _ _ _ _ OppositeSide_E_AB_R) as OppositeSide_E_BA_R.

	pose proof (lemma_righttogether _ _ _ _ RightTriangle_EAB RightTriangle_BAR OppositeSide_E_BA_R) as (_ & BetS_E_A_R).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_A_R) as BetS_R_A_E.
	pose proof (by_def_OnRay _ _ _ _ BetS_R_A_D BetS_R_A_E) as OnRay_AD_E.
	pose proof (lemma_layoffunique _ _ _ _ OnRay_AD_E OnRay_AD_D Cong_AE_AD) as eq_E_D.

	assert (Parallelogram A B c D) as Parallelogram_A_B_c_D by (rewrite <- eq_E_D; exact Parallelogram_A_B_c_E).

	assert (Square A B c D) as Square_A_B_c_D by (rewrite <- eq_E_D; exact Square_A_B_c_E).

	assert (Square_A_B_c_D_2 := Square_A_B_c_D).
	destruct Square_A_B_c_D_2 as (Cong_AB_cD & _ & _ & _ & _ & RightTriangle_BcD & RightTriangle_cDA).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AB_cD) as Cong_cD_AB.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_cD_AB Cong_AB_CD) as Cong_cD_CD.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_cD_CD) as (Cong_Dc_DC & _ & _).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_Dc_DC) as Cong_DC_Dc.

	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_BcD RightTriangle_BCD) as CongA_BcD_BCD.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_cDA) as RightTriangle_ADc.
	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_ADC RightTriangle_ADc) as CongA_ADC_ADc.

	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_cDA) as nCol_c_D_A.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_c_D_A) as (_ & _ & _ & neq_D_c & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_D_c) as OnRay_Dc_c.

	pose proof (proposition_04 _ _ _ _ _ _ Cong_cB_CB Cong_cD_CD CongA_BcD_BCD) as (
		_ & _ & CongA_cDB_CDB
	).
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_cDB_CDB) as CongA_CDB_cDB.

	pose proof (lemma_diagonalsbisect _ _ _ _ Parallelogram_A_B_c_D) as (m & Midpoint_A_m_c & Midpoint_B_m_D).

	pose proof (cn_congruencereflexive A m) as Cong_Am_Am.
	pose proof (cn_congruencereflexive D m) as Cong_Dm_Dm.

	destruct Midpoint_A_m_c as (BetS_A_m_c & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_m_c) as BetS_c_m_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_m_c) as (neq_m_c & neq_A_m & neq_A_c).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_c_m_A) as (neq_m_A & neq_c_m & neq_c_A).

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_A_m_c neq_A_m) as OnRay_Am_c.

	destruct Midpoint_B_m_D as (BetS_B_m_D & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_m_D) as BetS_D_m_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_m_D) as (neq_m_D & neq_B_m & neq_B_D).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_D_m_B) as (neq_m_B & neq_D_m & neq_D_B).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_m_D) as Col_B_m_D.
	pose proof (by_prop_Col_order _ _ _ Col_B_m_D) as (Col_m_B_D & Col_m_D_B & Col_D_B_m & Col_B_D_m & Col_D_m_B).

	pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_D_m_B neq_D_B) as OnRay_DB_m.


	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_cDB_CDB OnRay_DC_C OnRay_DB_m) as CongA_cDB_CDm.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_cDB_CDm) as CongA_CDm_cDB.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_CDm_cDB OnRay_Dc_c OnRay_DB_m) as CongA_CDm_cDm.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_CDm_cDm) as CongA_cDm_CDm.

	pose proof (proposition_04 _ _ _ _ _ _ Cong_Dc_DC Cong_Dm_Dm CongA_cDm_CDm) as (Cong_cm_Cm & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_cm_Cm) as (Cong_mc_mC & _ & _).

	pose proof (proposition_04 _ _ _ _ _ _ Cong_DA_DA Cong_DC_Dc CongA_ADC_ADc) as (Cong_AC_Ac & _ & _).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AC_Ac) as Cong_Ac_AC.

	pose proof (lemma_betweennesspreserved _ _ _ _ _ _ Cong_Am_Am Cong_Ac_AC Cong_mc_mC BetS_A_m_c) as BetS_A_m_C.

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_A_m_C neq_A_m) as OnRay_Am_C.

	pose proof (lemma_layoffunique _ _ _ _ OnRay_Am_c OnRay_Am_C Cong_Ac_AC) as eq_c_C.

	assert (Parallelogram A B C D) as Parallelogram_A_B_C_D by (rewrite <- eq_c_C; exact Parallelogram_A_B_c_D).

	exact Parallelogram_A_B_C_D.
Qed.

End Euclid.
