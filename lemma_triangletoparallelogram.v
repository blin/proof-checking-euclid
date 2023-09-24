Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col .
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_Par.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
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
	intros Par_D_C_E_F.
	intros Col_E_F_A.

	pose proof (by_prop_Par_NC _ _ _ _ Par_D_C_E_F) as (nCol_D_C_E & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_D_C_E) as (neq_D_C & _ & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_D_C) as neq_C_D.
	pose proof (lemma_extension C D C D neq_C_D neq_C_D) as (B & BetS_C_D_B & Cong_D_B_C_D).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_D_B) as BetS_B_D_C.
	pose proof (by_prop_Par_NC _ _ _ _ Par_D_C_E_F) as (_ & _ & nCol_C_E_F & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_C_E_F) as (_ & neq_E_F & _ & _ & _ & _).
	
	assert (Par_D_C_E_F_2 := Par_D_C_E_F).
	destruct Par_D_C_E_F_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_D_C_E_F & _ & _).

	assert (~ Col B C A) as n_Col_B_C_A.
	{
		intro Col_B_C_A.
		pose proof (by_def_Col_from_BetS_A_B_C C D B BetS_C_D_B) as Col_C_D_B.
		pose proof (by_prop_Col_order _ _ _ Col_C_D_B) as (_ & _ & Col_B_C_D & _ & _).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_B_D_C) as (_ & _ & neq_B_C).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_C_A Col_B_C_D neq_B_C) as Col_C_A_D.
		pose proof (by_prop_Col_order _ _ _ Col_C_A_D) as (_ & _ & Col_D_C_A & _ & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_D_C neq_E_F Col_D_C_A Col_E_F_A) as Meet_D_C_E_F.

		contradict Meet_D_C_E_F.
		exact n_Meet_D_C_E_F.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_B_C_A) as nCol_B_C_A.

	pose proof (proposition_31 _ _ _ _ BetS_B_D_C nCol_B_C_A) as (c & b & M & BetS_c_A_b & CongA_b_A_D_A_D_B & CongA_b_A_D_B_D_A & CongA_D_A_b_B_D_A & CongA_c_A_D_A_D_C & CongA_c_A_D_C_D_A & CongA_D_A_c_C_D_A & Par_c_b_B_C & Cong_c_A_D_C & Cong_A_b_B_D & Cong_A_M_M_D & Cong_c_M_M_C & Cong_B_M_M_b & BetS_c_M_C & BetS_B_M_b & BetS_A_M_D).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_b) as BetS_b_M_B.
	pose proof (by_prop_Par_NC _ _ _ _ Par_c_b_B_C) as (_ & _ & nCol_b_B_C & _).
	pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_b_M_B BetS_C_D_B nCol_b_B_C) as (R & BetS_b_R_D & BetS_C_R_M).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_M_C) as BetS_C_M_c.
	pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_C_R_M BetS_C_M_c) as BetS_C_R_c.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_A_b) as BetS_b_A_c.
	pose proof (by_prop_Par_NC _ _ _ _ Par_c_b_B_C) as (_ & _ & _ & nCol_c_b_C).
	pose proof (by_prop_nCol_order _ _ _ nCol_c_b_C) as (nCol_b_c_C & _ & _ & _ & _).
	pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_b_A_c BetS_C_R_c nCol_b_c_C) as (Q & BetS_b_Q_R & BetS_C_Q_A).
	pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_b_Q_R BetS_b_R_D) as BetS_b_Q_D.
	pose proof (by_def_Col_from_BetS_A_B_C C D B BetS_C_D_B) as Col_C_D_B.
	pose proof (by_prop_Col_order _ _ _ Col_C_D_B) as (_ & _ & Col_B_C_D & _ & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_c_b_B_C Col_B_C_D neq_D_C) as Par_c_b_D_C.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_c_b_D_C) as Par_D_C_c_b.
	pose proof (by_def_Col_from_BetS_A_B_C c A b BetS_c_A_b) as Col_c_A_b.
	pose proof (by_prop_Col_order _ _ _ Col_c_A_b) as (_ & _ & _ & Col_c_b_A & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_c_A_b) as (neq_A_b & _ & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_D_C_c_b Col_c_b_A neq_A_b) as Par_D_C_A_b.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_D_C_A_b) as Par_A_b_D_C.
	pose proof (by_prop_Par_flip _ _ _ _ Par_A_b_D_C) as (_ & _ & Par_b_A_C_D).
	pose proof (cn_congruencereverse B D) as Cong_B_D_D_B.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_A_b_B_D Cong_B_D_D_B) as Cong_A_b_D_B.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_A_b_D_B Cong_D_B_C_D) as Cong_A_b_C_D.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_A_b_C_D) as (_ & Cong_b_A_C_D & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_Q_A) as BetS_A_Q_C.
	pose proof (proposition_33 _ _ _ _ _ Par_b_A_C_D Cong_b_A_C_D BetS_b_Q_D BetS_A_Q_C) as (Par_b_C_A_D & Cong_b_C_A_D).
	pose proof (by_prop_Par_flip _ _ _ _ Par_b_A_C_D) as (Par_A_b_C_D & _ & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_b_C_A_D) as Par_A_D_b_C.
	pose proof (by_def_Parallelogram _ _ _ _ Par_A_b_C_D Par_A_D_b_C) as Parallelogram_A_b_C_D.
	assert (eq E E) as eq_E_E by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C E F E eq_E_E) as Col_E_F_E.

	(* assert by cases *)
	assert (Col E F b) as Col_E_F_b.
	assert (eq A F \/ neq A F) as [eq_A_F|neq_A_F] by (apply Classical_Prop.classic).
	{
		(* case eq_A_F *)
		pose proof (by_prop_neq_symmetric _ _ neq_E_F) as neq_F_E.
		assert (neq A E) as neq_A_E by (rewrite eq_A_F; exact neq_F_E).
		pose proof (by_prop_Par_collinear2 _ _ _ _ _ _ Par_D_C_E_F Col_E_F_A Col_E_F_E neq_A_E) as Par_D_C_A_E.
		pose proof (lemma_Playfair _ _ _ _ _ Par_D_C_A_b Par_D_C_A_E) as Col_A_b_E.
		assert (Col F b E) as Col_F_b_E by (rewrite <- eq_A_F; exact Col_A_b_E).
		pose proof (by_prop_Col_order _ _ _ Col_F_b_E) as (_ & _ & Col_E_F_b & _ & _).

		exact Col_E_F_b.
	}
	{
		(* case neq_A_F *)
		pose proof (by_prop_Par_collinear _ _ _ _ _ Par_D_C_E_F Col_E_F_A neq_A_F) as Par_D_C_A_F.
		pose proof (lemma_Playfair _ _ _ _ _ Par_D_C_A_b Par_D_C_A_F) as Col_A_b_F.
		pose proof (by_prop_Col_order _ _ _ Col_A_b_F) as (_ & _ & _ & Col_A_F_b & _).
		pose proof (by_prop_Col_order _ _ _ Col_E_F_A) as (_ & _ & _ & _ & Col_A_F_E).
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

