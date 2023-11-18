Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_flip.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_collinear.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_Square_flip.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_droppedperpendicularunique.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_squareparallelogram.
Require Import ProofCheckingEuclid.proposition_47B.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_47 :
	forall A B C D E F G H K,
	Triangle A B C ->
	RightTriangle B A C ->
	Square A B F G ->
	OppositeSide G B A C ->
	Square A C K H ->
	OppositeSide H C A B ->
	Square B C E D ->
	OppositeSide D C B A ->
	exists X Y, (
		Parallelogram B X Y D /\
		BetS B X C /\
		Parallelogram X C E Y /\
		BetS D Y E /\
		EqAreaQuad A B F G B X Y D /\
		EqAreaQuad A C K H X C E Y
	).
Proof.
	intros A B C D E F G H K.
	intros Triangle_ABC.
	intros RightTriangle_BAC.
	intros Square_A_B_F_G.
	intros OppositeSide_G_BA_C.
	intros Square_A_C_K_H.
	intros OppositeSide_H_CA_B.
	intros Square_B_C_E_D.
	intros OppositeSide_D_CB_A.

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_ABC) as nCol_A_B_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (_ & _ & _ & nCol_A_C_B & _).
	pose proof (by_def_Triangle _ _ _ nCol_A_C_B) as Triangle_ACB.
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_C) as n_Col_A_B_C.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_BAC) as RightTriangle_CAB.

	pose proof (by_prop_Square_flip _ _ _ _ Square_B_C_E_D) as Square_C_B_D_E.

	pose proof (lemma_squareparallelogram _ _ _ _ Square_B_C_E_D) as Parallelogram_B_C_E_D.
	assert (Parallelogram_B_C_E_D_2 := Parallelogram_B_C_E_D).
	destruct Parallelogram_B_C_E_D_2 as (Par_BC_ED &_ ).
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_BC_ED) as TarskiPar_BC_ED.
	assert (TarskiPar_BC_ED_2 := TarskiPar_BC_ED).
	destruct TarskiPar_BC_ED_2 as (_ & neq_E_D & _ & SameSide_E_D_BC).

	pose proof (by_prop_neq_symmetric _ _ neq_E_D) as neq_D_E.

	pose proof (by_prop_OppositeSide_flip _ _ _ _ OppositeSide_D_CB_A) as OppositeSide_D_BC_A.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_E_D_BC OppositeSide_D_BC_A) as OppositeSide_E_BC_A.

	pose proof (
		proposition_47B
		_ _ _ _ _ _ _
		Triangle_ABC RightTriangle_BAC Square_A_B_F_G OppositeSide_G_BA_C Square_B_C_E_D OppositeSide_D_CB_A
	) as (
		M & L &
		Parallelogram_B_M_L_D & BetS_B_M_C &
		Parallelogram_M_C_E_L & BetS_D_L_E &
		BetS_L_M_A & RightTriangle_DLA &
		EqAreaQuad_ABFG_BMLD
	).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_C) as BetS_C_M_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_M_C) as (neq_M_C & neq_B_M & neq_B_C).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_M_B) as (neq_M_B & neq_C_M & neq_C_B).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_M_C) as Col_B_M_C.
	pose proof (by_prop_Col_order _ _ _ Col_B_M_C) as (Col_M_B_C & Col_M_C_B & Col_C_B_M & Col_B_C_M & Col_C_M_B).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_L_E) as BetS_E_L_D.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_L_D) as (neq_L_D & neq_E_L & _).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_D_L_E) as Col_D_L_E.
	pose proof (by_prop_Col_order _ _ _ Col_D_L_E) as (Col_L_D_E & Col_L_E_D & Col_E_D_L & Col_D_E_L & Col_E_L_D).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_L_M_A) as (neq_M_A & neq_L_M & neq_L_A).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_L_M_A) as Col_L_M_A.
	pose proof (by_prop_Col_order _ _ _ Col_L_M_A) as (Col_M_L_A & Col_M_A_L & Col_A_L_M & Col_L_A_M & Col_A_M_L).

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_DLA Col_D_L_E neq_E_L) as RightTriangle_ELA.

	pose proof (
		proposition_47B
		_ _ _ _ _ _ _
		Triangle_ACB RightTriangle_CAB Square_A_C_K_H OppositeSide_H_CA_B Square_C_B_D_E OppositeSide_E_BC_A
	) as (
		m & l &
		_ & BetS_C_m_B &
		_ & BetS_E_l_D &
		BetS_l_m_A & RightTriangle_ElA &
		EqAreaQuad_ACKH_CmlE
	).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_m_B) as (neq_m_B & neq_C_m & _).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_m_B) as Col_C_m_B.
	pose proof (by_prop_Col_order _ _ _ Col_C_m_B) as (Col_m_C_B & Col_m_B_C & Col_B_C_m & Col_C_B_m & Col_B_m_C).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_l_D) as BetS_D_l_E.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_E_l_D) as (neq_l_D & neq_E_l & _).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_E_l_D) as Col_E_l_D.
	pose proof (by_prop_Col_order _ _ _ Col_E_l_D) as (Col_l_E_D & Col_l_D_E & Col_D_E_l & Col_E_D_l & Col_D_l_E).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_E_l Col_D_E_L neq_D_E) as Col_E_l_L.

	pose proof (lemma_droppedperpendicularunique _ _ _ _ RightTriangle_ElA RightTriangle_ELA Col_E_l_L) as eq_l_L.

	assert (BetS L m A) as BetS_L_m_A by (rewrite <- eq_l_L; exact BetS_l_m_A).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_L_m_A) as Col_L_m_A.
	pose proof (by_prop_Col_order _ _ _ Col_L_m_A) as (Col_m_L_A & Col_m_A_L & Col_A_L_m & Col_L_A_m & Col_A_m_L).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_L_A_m Col_L_A_M neq_L_A) as Col_A_m_M.
	pose proof (by_prop_Col_order _ _ _ Col_A_m_M) as (_ & _ & _ & _ & Col_M_m_A).
	pose proof (by_prop_Col_order _ _ _ Col_M_m_A) as (Col_m_M_A & _ & _ & _ & _).

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_B_M Col_C_B_m neq_C_B) as Col_B_M_m.
	pose proof (by_prop_Col_order _ _ _ Col_B_M_m) as (_ & Col_M_m_B & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_M_m_B) as (Col_m_M_B & _ & _ & _ & _).

	assert (~ neq M m) as n_neq_M_m.
	{
		intro neq_M_m.

		pose proof (by_prop_neq_symmetric _ _ neq_M_m) as neq_m_M.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_m_M_A Col_m_M_B neq_m_M) as Col_M_A_B.
		pose proof (by_prop_Col_order _ _ _ Col_M_A_B) as (_ & _ & _ & Col_M_B_A & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_M_B_A Col_M_B_C neq_M_B) as Col_B_A_C.
		pose proof (by_prop_Col_order _ _ _ Col_B_A_C) as (Col_A_B_C & _ & _ & _ & _).

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	assert (eq_M_m := n_neq_M_m).
	apply Classical_Prop.NNPP in eq_M_m.


	assert (EqAreaQuad A C K H C M l E) as EqAreaQuad_ACKH_CMlE by (rewrite eq_M_m; exact EqAreaQuad_ACKH_CmlE).
	assert (EqAreaQuad A C K H C M L E) as EqAreaQuad_ACKH_CMLE by (rewrite <- eq_l_L; exact EqAreaQuad_ACKH_CMlE).

	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_ACKH_CMLE) as (
		_ & _ & _ & EqAreaQuad_ACKH_MCEL & _ & _ & _
	).

	exists M, L.
	split.
	exact Parallelogram_B_M_L_D.
	split.
	exact BetS_B_M_C.
	split.
	exact Parallelogram_M_C_E_L.
	split.
	exact BetS_D_L_E.
	split.
	exact EqAreaQuad_ABFG_BMLD.
	exact EqAreaQuad_ACKH_MCEL.
Qed.

End Euclid.
