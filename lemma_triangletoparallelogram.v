Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_Par.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col .
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_collinear2.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Playfair.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.proposition_31.
Require Import ProofCheckingEuclid.proposition_33.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_triangletoparallelogram :
	forall A C D E F,
	Par D C E F ->
	Col E F A ->
	exists X, Parallelogram A X C D /\ Col E F X.
Proof.
	intros A C D E F.
	intros Par_DC_EF.
	intros Col_E_F_A.

	assert (eq E E) as eq_E_E by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C E F E eq_E_E) as Col_E_F_E.

	pose proof (by_prop_Col_order _ _ _ Col_E_F_A) as (_ & _ & _ & _ & Col_A_F_E).

	pose proof (by_prop_Par_NC _ _ _ _ Par_DC_EF) as (nCol_D_C_E & _ & _ & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_DC_EF) as (_ & _ & nCol_C_E_F & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_D_C_E) as (neq_D_C & _ & _ & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_C_E_F) as (_ & neq_E_F & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_E_F) as neq_F_E.
	pose proof (by_prop_neq_symmetric _ _ neq_D_C) as neq_C_D.

	pose proof (lemma_extension _ _ _ _ neq_C_D neq_C_D) as (B & BetS_C_D_B & Cong_DB_CD).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_D_B) as BetS_B_D_C.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_D_C) as (_ & _ & neq_B_C).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_D_B) as Col_C_D_B.
	pose proof (by_prop_Col_order _ _ _ Col_C_D_B) as (_ & _ & Col_B_C_D & _ & _).


	assert (Par_DC_EF_2 := Par_DC_EF).
	destruct Par_DC_EF_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_D_C_E_F & _ & _).

	assert (~ Col B C A) as n_Col_B_C_A.
	{
		intro Col_B_C_A.

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_C_A Col_B_C_D neq_B_C) as Col_C_A_D.
		pose proof (by_prop_Col_order _ _ _ Col_C_A_D) as (_ & _ & Col_D_C_A & _ & _).

		pose proof (by_def_Meet _ _ _ _ _ neq_D_C neq_E_F Col_D_C_A Col_E_F_A) as Meet_D_C_E_F.

		contradict Meet_D_C_E_F.
		exact n_Meet_D_C_E_F.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_B_C_A) as nCol_B_C_A.

	pose proof (proposition_31 _ _ _ _ BetS_B_D_C nCol_B_C_A) as (
		c & b & M &
		BetS_c_A_b &
		_ & _ & _ & _ & _ & _ &
		Par_cb_BC &
		_ & Cong_Ab_BD & _ & _ & _ &
		BetS_c_M_C & BetS_B_M_b & _
	).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_A_b) as BetS_b_A_c.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_c_A_b) as Col_c_A_b.
	pose proof (by_prop_Col_order _ _ _ Col_c_A_b) as (_ & _ & _ & Col_c_b_A & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_c_A_b) as (neq_A_b & _ & _).

	pose proof (by_prop_Par_NC _ _ _ _ Par_cb_BC) as (_ & _ & nCol_b_B_C & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_cb_BC) as (_ & _ & _ & nCol_c_b_C).
	pose proof (by_prop_nCol_order _ _ _ nCol_c_b_C) as (nCol_b_c_C & _ & _ & _ & _).

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_cb_BC Col_B_C_D neq_D_C) as Par_cb_DC.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_cb_DC) as Par_DC_cb.

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_DC_cb Col_c_b_A neq_A_b) as Par_DC_Ab.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_DC_Ab) as Par_Ab_DC.
	pose proof (by_prop_Par_flip _ _ _ _ Par_Ab_DC) as (_ & _ & Par_bA_CD).
	pose proof (by_prop_Par_flip _ _ _ _ Par_bA_CD) as (Par_Ab_CD & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_M_C) as BetS_C_M_c.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_b) as BetS_b_M_B.

	pose proof (cn_congruencereverse B D) as Cong_BD_DB.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_Ab_BD Cong_BD_DB) as Cong_Ab_DB.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_Ab_DB Cong_DB_CD) as Cong_Ab_CD.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_Ab_CD) as (_ & Cong_bA_CD & _).


	pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_b_M_B BetS_C_D_B nCol_b_B_C) as (R & BetS_b_R_D & BetS_C_R_M).

	pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_C_R_M BetS_C_M_c) as BetS_C_R_c.

	pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_b_A_c BetS_C_R_c nCol_b_c_C) as (Q & BetS_b_Q_R & BetS_C_Q_A).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_Q_A) as BetS_A_Q_C.

	pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_b_Q_R BetS_b_R_D) as BetS_b_Q_D.

	pose proof (proposition_33 _ _ _ _ _ Par_bA_CD Cong_bA_CD BetS_b_Q_D BetS_A_Q_C) as (Par_bC_AD & _).

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_bC_AD) as Par_AD_bC.
	pose proof (by_def_Parallelogram _ _ _ _ Par_Ab_CD Par_AD_bC) as Parallelogram_A_b_C_D.


	(* assert by cases *)
	assert (Col E F b) as Col_E_F_b.
	assert (eq A F \/ neq A F) as [eq_A_F|neq_A_F] by (apply Classical_Prop.classic).
	{
		(* case eq_A_F *)
		assert (neq A E) as neq_A_E by (rewrite eq_A_F; exact neq_F_E).

		pose proof (by_prop_Par_collinear2 _ _ _ _ _ _ Par_DC_EF Col_E_F_A Col_E_F_E neq_A_E) as Par_DC_AE.

		pose proof (lemma_Playfair _ _ _ _ _ Par_DC_Ab Par_DC_AE) as Col_A_b_E.

		assert (Col F b E) as Col_F_b_E by (rewrite <- eq_A_F; exact Col_A_b_E).
		pose proof (by_prop_Col_order _ _ _ Col_F_b_E) as (_ & _ & Col_E_F_b & _ & _).

		exact Col_E_F_b.
	}
	{
		(* case neq_A_F *)
		pose proof (by_prop_Par_collinear _ _ _ _ _ Par_DC_EF Col_E_F_A neq_A_F) as Par_DC_AF.

		pose proof (lemma_Playfair _ _ _ _ _ Par_DC_Ab Par_DC_AF) as Col_A_b_F.
		pose proof (by_prop_Col_order _ _ _ Col_A_b_F) as (_ & _ & _ & Col_A_F_b & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_F_b Col_A_F_E neq_A_F) as Col_F_b_E.
		pose proof (by_prop_Col_order _ _ _ Col_F_b_E) as (_ & _ & Col_E_F_b & _ & _).

		exact Col_E_F_b.
	}

	exists b.
	split.
	exact Parallelogram_A_b_C_D.
	exact Col_E_F_b.
Qed.

End Euclid.
