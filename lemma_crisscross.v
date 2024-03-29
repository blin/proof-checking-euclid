Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Cross.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABD_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_planeseparation.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_crisscross :
	forall A B C D,
	Par A C B D ->
	~ Cross A B C D ->
	Cross A D B C.
Proof.
	intros A B C D.
	intros Par_AC_BD.
	intros n_Cross_AB_CD.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq D D) as eq_D_D by (reflexivity).

	pose proof (by_def_Col_from_eq_A_B B B D eq_B_B) as Col_B_B_D.
	pose proof (by_def_Col_from_eq_A_C A B A eq_A_A) as Col_A_B_A.
	pose proof (by_def_Col_from_eq_A_C B D B eq_B_B) as Col_B_D_B.
	pose proof (by_def_Col_from_eq_A_C D B D eq_D_D) as Col_D_B_D.
	pose proof (by_def_Col_from_eq_B_C A C C eq_C_C) as Col_A_C_C.
	pose proof (by_def_Col_from_eq_B_C C A A eq_A_A) as Col_C_A_A.

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_AC_BD) as Par_BD_AC.
	pose proof (by_prop_Par_flip _ _ _ _ Par_AC_BD) as (Par_CA_BD & _ & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AC_BD) as (nCol_A_C_B & nCol_A_B_D & _ & nCol_A_C_D).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_C_B) as (neq_A_C & neq_C_B & neq_A_B & neq_C_A & neq_B_C & neq_B_A).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_C_B) as (nCol_C_A_B & nCol_C_B_A & nCol_B_A_C & nCol_A_B_C & nCol_B_C_A).
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_C_B) as n_Col_A_C_B.

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_D) as (_ & neq_B_D & neq_A_D & _ & neq_D_B & neq_D_A).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_D) as (nCol_B_A_D & nCol_B_D_A & nCol_D_A_B & nCol_A_D_B & nCol_D_B_A).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_C_D) as (_ & neq_C_D & _ & _ & neq_D_C & _).

	destruct Par_CA_BD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_C_A_B_D & _ & _).

	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_BD_AC) as TarskiPar_BD_AC.
	destruct TarskiPar_BD_AC as (_ & _ & _ & SameSide_A_C_BD).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_A_C_BD) as (SameSide_C_A_BD & _ & _).

	pose proof (postulate_Euclid2 _ _ neq_A_B) as (E & BetS_A_B_E).

	assert (eq E E) as eq_E_E by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C A E E eq_E_E) as Col_A_E_E.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_E) as BetS_E_B_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_B_E) as (_ & _ & neq_A_E).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_B_E) as (neq_B_E & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_A_E) as neq_E_A.
	pose proof (by_prop_neq_symmetric _ _ neq_B_E) as neq_E_B.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_B_E) as Col_A_B_E.
	pose proof (by_prop_Col_order _ _ _ Col_A_B_E) as (Col_B_A_E & Col_B_E_A & Col_E_A_B & Col_A_E_B & Col_E_B_A).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_B_C Col_A_B_A Col_A_B_E neq_A_E) as nCol_A_E_C.
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_B_D Col_A_B_A Col_A_B_E neq_A_E) as nCol_A_E_D.
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_E_C Col_A_E_B Col_A_E_E neq_B_E) as nCol_B_E_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_E_C) as (nCol_E_A_C & nCol_E_C_A & nCol_C_A_E & nCol_A_C_E & nCol_C_E_A).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_E_D) as (nCol_E_A_D & nCol_E_D_A & nCol_D_A_E & nCol_A_D_E & nCol_D_E_A).
	pose proof (by_prop_nCol_order _ _ _ nCol_B_E_C) as (nCol_E_B_C & nCol_E_C_B & nCol_C_B_E & nCol_B_C_E & nCol_C_E_B).

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_A_B_E Col_B_D_B nCol_B_D_A) as OppositeSide_A_BD_E.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_C_A_BD OppositeSide_A_BD_E) as OppositeSide_C_BD_E.

	destruct OppositeSide_C_BD_E as (F & BetS_C_F_E & Col_B_D_F & nCol_B_D_C).

	assert (eq F F) as eq_F_F by (reflexivity).
	pose proof (by_def_Col_from_eq_A_B F F D eq_F_F) as Col_F_F_D.
	pose proof (by_def_Col_from_eq_A_C C F C eq_C_C) as Col_C_F_C.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_F_E) as BetS_E_F_C.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_F_E) as (_ & _ & neq_C_E).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_F_E) as (neq_F_E & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_F_E) as neq_E_F.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_F_E) as Col_C_F_E.
	pose proof (by_prop_Col_order _ _ _ Col_C_F_E) as (_ & _ & _ & _ & Col_E_F_C).

	pose proof (by_prop_Col_order _ _ _ Col_B_D_F) as (Col_D_B_F & _ & _ & _ & _).

	pose proof (by_prop_nCol_order _ _ _ nCol_B_D_C) as (nCol_D_B_C & _ & _ & _ & _).

	(* assert by cases *)
	assert (Cross A D B C) as Cross_AD_BC.
	assert (Col_B_D_F_2 := Col_B_D_F).
	destruct Col_B_D_F_2 as [eq_B_D | [eq_B_F | [eq_D_F | [BetS_D_B_F | [BetS_B_D_F | BetS_B_F_D]]]]].
	{
		(* case eq_B_D *)
		contradict eq_B_D.
		exact neq_B_D.
	}
	{
		(* case eq_B_F *)
		assert (Col E B C) as Col_E_B_C by (rewrite eq_B_F; exact Col_E_F_C).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_E_B_A Col_E_B_C neq_E_B) as Col_B_A_C.
		pose proof (by_prop_Col_order _ _ _ Col_B_A_C) as (_ & Col_A_C_B & _ & _ & _).

		contradict Col_A_C_B.
		exact n_Col_A_C_B.
	}
	{
		(* case eq_D_F *)
		assert (nCol A C F) as nCol_A_C_F by (rewrite <- eq_D_F; exact nCol_A_C_D).
		pose proof (by_prop_nCol_order _ _ _ nCol_A_C_F) as (_ & nCol_C_F_A & _ & _ & _).

		pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_A_B_E BetS_C_F_E nCol_A_E_C) as (M & BetS_A_M_F & BetS_C_M_B).
		assert (BetS A M D) as BetS_A_M_D by (rewrite eq_D_F; exact BetS_A_M_F).
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_M_B) as BetS_B_M_C.

		pose proof (by_def_Cross _ _ _ _ _ BetS_A_M_D BetS_B_M_C) as Cross_AD_BC.

		exact Cross_AD_BC.
	}
	{
		(* case BetS_D_B_F *)
		pose proof (by_prop_BetS_notequal _ _ _ BetS_D_B_F) as (_ & _ & neq_D_F).

		pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_D_B_C Col_D_B_D Col_D_B_F neq_D_F) as nCol_D_F_C.
		pose proof (by_prop_nCol_order _ _ _ nCol_D_F_C) as (_ & _ & _ & _ & nCol_C_F_D).
		pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_C_F_D Col_C_F_C Col_C_F_E neq_C_E) as nCol_C_E_D.
		pose proof (by_prop_nCol_order _ _ _ nCol_C_E_D) as (nCol_E_C_D & _ & _ & _ & _).

		pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_D_B_F BetS_E_F_C nCol_E_C_D) as (M & BetS_D_M_C & BetS_E_B_M).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_M_C) as BetS_C_M_D.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_B_M) as BetS_M_B_E.

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_B_M) as Col_E_B_M.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_E_B_M Col_E_B_A neq_E_B) as Col_B_M_A.
		pose proof (by_prop_Col_order _ _ _ Col_B_M_A) as (_ & _ & Col_A_B_M & _ & _).

		pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_C_A_A Col_B_B_D neq_C_A neq_B_D neq_C_A neq_B_D n_Meet_C_A_B_D BetS_C_M_D Col_A_B_M) as BetS_A_M_B.

		pose proof (by_def_Cross _ _ _ _ _ BetS_A_M_B BetS_C_M_D) as Cross_AB_CD.

		contradict Cross_AB_CD.
		exact n_Cross_AB_CD.
	}
	{
		(* case BetS_B_D_F *)

		pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_B_D_F BetS_C_F_E nCol_C_E_B) as (J & BetS_B_J_E & BetS_C_D_J).

		pose proof (lemma_orderofpoints_ABD_BCD_ACD _ _ _ _ BetS_A_B_E BetS_B_J_E) as BetS_A_J_E.
		pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_A_B_E BetS_B_J_E) as BetS_A_B_J.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_A_J_E) as (_ & neq_A_J & _).

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_J_E) as Col_A_J_E.
		pose proof (by_prop_Col_order _ _ _ Col_A_J_E) as (_ & _ & Col_E_A_J & _ & _).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_E_A_B Col_E_A_J neq_E_A) as Col_A_B_J.
		pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_B_C Col_A_B_A Col_A_B_J neq_A_J) as nCol_A_J_C.

		pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_A_B_J BetS_C_D_J nCol_A_J_C) as (M & BetS_A_M_D & BetS_C_M_B).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_M_B) as BetS_B_M_C.

		pose proof (by_def_Cross _ _ _ _ _ BetS_A_M_D BetS_B_M_C) as Cross_AD_BC.

		exact Cross_AD_BC.
	}
	{
		(* case BetS_B_F_D *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_F_D) as BetS_D_F_B.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_B_F_D) as (neq_F_D & _ & _).

		pose proof (by_prop_Par_collinear _ _ _ _ _ Par_AC_BD Col_B_D_F neq_F_D) as Par_AC_FD.

		destruct Par_AC_FD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_A_C_F_D & _ & _).

		pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_D_F_B BetS_E_B_A nCol_E_A_D) as (Q & BetS_D_Q_A & BetS_E_F_Q).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_Q_A) as BetS_A_Q_D.

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_F_Q) as Col_E_F_Q.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_E_F_Q Col_E_F_C neq_E_F) as Col_F_Q_C.
		pose proof (by_prop_Col_order _ _ _ Col_F_Q_C) as (_ & _ & _ & Col_F_C_Q & _).
		pose proof (by_prop_Col_order _ _ _ Col_F_C_Q) as (Col_C_F_Q & _ & _ & _ & _).

		pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_A_C_C Col_F_F_D neq_A_C neq_F_D neq_A_C neq_F_D n_Meet_A_C_F_D BetS_A_Q_D Col_C_F_Q) as BetS_C_Q_F.

		pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_C_Q_F BetS_C_F_E) as BetS_C_Q_E.

		pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_A_B_E BetS_C_Q_E nCol_A_E_C) as (M & BetS_A_M_Q & BetS_C_M_B).

		pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_A_M_Q BetS_A_Q_D) as BetS_A_M_D.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_M_B) as BetS_B_M_C.

		pose proof (by_def_Cross _ _ _ _ _ BetS_A_M_D BetS_B_M_C) as Cross_AD_BC.

		exact Cross_AD_BC.
	}

	exact Cross_AD_BC.
Qed.

End Euclid.
