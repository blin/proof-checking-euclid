Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_otherside_betweenness_PABC_RPQ_QABC.
Require Import ProofCheckingEuclid.lemma_otherside_betweenness_PABC_RQP_QABC.
Require Import ProofCheckingEuclid.lemma_outerconnectivity.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_twolines2.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.


Lemma lemma_planeseparation_Col_C_Q_D : 
	forall A B C D E Q G H,
	OS D A B E ->
	Col A B G ->
	Col A B H ->
	BetS C G Q ->
	BetS D H Q ->
	nCol A B C ->
	nCol A B D ->
	Col C Q D ->
	neq C D ->
	OS C A B E.
Proof.
	intros A B C D E Q G H.
	intros OS_D_AB_E.
	intros Col_A_B_G.
	intros Col_A_B_H.
	intros BetS_C_G_Q.
	intros BetS_D_H_Q.
	intros nCol_A_B_C.
	intros nCol_A_B_D.
	intros Col_C_Q_D.
	intros neq_C_D.

	assert (OS_D_AB_E2 := OS_D_AB_E).
	destruct OS_D_AB_E2 as (W & BetS_D_W_E & Col_A_B_W & _).

	pose proof (lemma_betweennotequal _ _ _ BetS_D_W_E) as (neq_W_E & neq_D_W & neq_D_E).
	assert (Col D W E) as Col_D_W_E by (unfold Col; one_of_disjunct BetS_D_W_E).
	pose proof (lemma_collinearorder _ _ _ Col_D_W_E) as (Col_W_D_E & Col_W_E_D & Col_E_D_W & Col_D_E_W & Col_E_W_D).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_W_E) as BetS_E_W_D.
	pose proof (lemma_collinearorder _ _ _ Col_A_B_W) as (Col_B_A_W & Col_B_W_A & Col_W_A_B & Col_A_W_B & Col_W_B_A).

	pose proof (lemma_collinearorder _ _ _ Col_A_B_G) as (Col_B_A_G & Col_B_G_A & Col_G_A_B & Col_A_G_B & Col_G_B_A).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_H) as (Col_B_A_H & Col_B_H_A & Col_H_A_B & Col_A_H_B & Col_H_B_A).

	pose proof (lemma_betweennotequal _ _ _ BetS_C_G_Q) as (neq_G_Q & neq_C_G & neq_C_Q).
	pose proof (lemma_betweennotequal _ _ _ BetS_D_H_Q) as (neq_H_Q & neq_D_H & neq_D_Q).
	assert (Col C G Q) as Col_C_G_Q by (unfold Col; one_of_disjunct BetS_C_G_Q).
	assert (Col D H Q) as Col_D_H_Q by (unfold Col; one_of_disjunct BetS_D_H_Q).
	pose proof (lemma_collinearorder _ _ _ Col_C_G_Q) as (Col_G_C_Q & Col_G_Q_C & Col_Q_C_G & Col_C_Q_G & Col_Q_G_C).
	pose proof (lemma_collinearorder _ _ _ Col_D_H_Q) as (Col_H_D_Q & Col_H_Q_D & Col_Q_D_H & Col_D_Q_H & Col_Q_H_D).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_G_Q) as BetS_Q_G_C.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_H_Q) as BetS_Q_H_D.

	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_D) as (_ & neq_B_D & neq_A_D & _ & neq_D_B & neq_D_A).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_D) as (nCol_B_A_D & nCol_B_D_A & nCol_D_A_B & nCol_A_D_B & nCol_D_B_A).


	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_D) as n_Col_A_B_D.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_C_A_B) as n_Col_C_A_B.

	pose proof (lemma_inequalitysymmetric _ _ neq_C_G) as neq_G_C.
	pose proof (lemma_inequalitysymmetric _ _ neq_C_Q) as neq_Q_C.
	pose proof (lemma_inequalitysymmetric _ _ neq_D_E) as neq_E_D.
	pose proof (lemma_inequalitysymmetric _ _ neq_D_H) as neq_H_D.
	pose proof (lemma_inequalitysymmetric _ _ neq_D_Q) as neq_Q_D.
	pose proof (lemma_inequalitysymmetric _ _ neq_D_W) as neq_W_D.
	pose proof (lemma_inequalitysymmetric _ _ neq_H_Q) as neq_Q_H.
	pose proof (lemma_inequalitysymmetric _ _ neq_W_E) as neq_E_W.

	pose proof (lemma_collinearorder _ _ _ Col_C_Q_D) as (Col_Q_C_D & Col_Q_D_C & Col_D_C_Q & Col_C_D_Q & Col_D_Q_C).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_C_G Col_Q_C_D neq_Q_C) as Col_C_G_D.
	pose proof (lemma_collinearorder _ _ _ Col_C_G_D) as (Col_G_C_D & Col_G_D_C & Col_D_C_G & Col_C_D_G & Col_D_G_C).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_Q_H Col_D_Q_C neq_D_Q) as Col_Q_H_C.
	pose proof (lemma_collinearorder _ _ _ Col_Q_H_C) as (Col_H_Q_C & Col_H_C_Q & Col_C_Q_H & Col_Q_C_H & Col_C_H_Q).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_D_C Col_Q_D_H neq_Q_D) as Col_D_C_H.
	pose proof (lemma_collinearorder _ _ _ Col_D_C_H) as (Col_C_D_H & Col_C_H_D & Col_H_D_C & Col_D_H_C & Col_H_C_D).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_W Col_A_B_G neq_A_B) as Col_B_W_G.
	pose proof (lemma_collinearorder _ _ _ Col_B_W_G) as (Col_W_B_G & Col_W_G_B & Col_G_B_W & Col_B_G_W & Col_G_W_B).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_W Col_B_A_G neq_B_A) as Col_A_W_G.
	pose proof (lemma_collinearorder _ _ _ Col_A_W_G) as (Col_W_A_G & Col_W_G_A & Col_G_A_W & Col_A_G_W & Col_G_W_A).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_H Col_B_A_G neq_B_A) as Col_A_H_G.
	pose proof (lemma_collinearorder _ _ _ Col_A_H_G) as (Col_H_A_G & Col_H_G_A & Col_G_A_H & Col_A_G_H & Col_G_H_A).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_H Col_A_B_G neq_A_B) as Col_B_H_G.
	pose proof (lemma_collinearorder _ _ _ Col_B_H_G) as (Col_H_B_G & Col_H_G_B & Col_G_B_H & Col_B_G_H & Col_G_H_B).

	assert (~ (Col C A B /\ Col D A B)) as n_Col_C_A_B_and_Col_D_A_B.
	{
		intros (Col_C_A_B & Col_D_A_B).
		contradict n_Col_C_A_B.
		exact Col_C_A_B.
	}
	pose proof (
		lemma_twolines2
		C D A B G H
		neq_C_D neq_A_B
		Col_G_C_D Col_G_A_B
		Col_H_C_D Col_H_A_B
		n_Col_C_A_B_and_Col_D_A_B
	) as eq_G_H.

	assert (BetS Q G D) as BetS_Q_G_D by (rewrite eq_G_H; exact BetS_Q_H_D).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_Q_G_D) as BetS_D_G_Q.
	pose proof (lemma_betweennotequal _ _ _ BetS_Q_G_D) as (neq_G_D & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_G_D) as neq_D_G.

	assert (Col Q G D) as Col_Q_G_D by (unfold Col; one_of_disjunct BetS_Q_G_D).
	pose proof (lemma_collinearorder _ _ _ Col_Q_G_D) as (Col_G_Q_D & Col_G_D_Q & Col_D_Q_G & Col_Q_D_G & Col_D_G_Q).

	assert (Col E D G \/ ~ Col E D G) as [Col_E_D_G|n_Col_E_D_G] by (apply Classical_Prop.classic).
	{
		(* case Col_E_D_G *)
		pose proof (lemma_collinearorder _ _ _ Col_E_D_G) as (Col_D_E_G & Col_D_G_E & Col_G_E_D & Col_E_G_D & Col_G_D_E).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_G_E Col_D_G_Q neq_D_G) as Col_G_E_Q.
		pose proof (lemma_collinearorder _ _ _ Col_G_E_Q) as (Col_E_G_Q & Col_E_Q_G & Col_Q_G_E & Col_G_Q_E & Col_Q_E_G).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_E_W Col_D_E_G neq_D_E) as Col_E_W_G.
		pose proof (lemma_collinearorder _ _ _ Col_E_W_G) as (Col_W_E_G & Col_W_G_E & Col_G_E_W & Col_E_G_W & Col_G_W_E).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_W_G Col_E_W_D neq_E_W) as Col_W_G_D.
		pose proof (lemma_collinearorder _ _ _ Col_W_G_D) as (Col_G_W_D & Col_G_D_W & Col_D_W_G & Col_W_D_G & Col_D_G_W).

		assert (~ ~ eq W G) as eq_W_G.
		{
			intros neq_W_G.

			assert (~ ~ eq G B) as eq_G_B.
			{
				intros neq_G_B.
				(* case neq_G_B *)
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_W_G_D Col_W_G_B neq_W_G) as Col_G_D_B.
				pose proof (lemma_collinearorder _ _ _ Col_G_D_B) as (Col_D_G_B & Col_D_B_G & Col_B_G_D & Col_G_B_D & Col_B_D_G).
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_B_D Col_G_B_A neq_G_B) as Col_B_D_A.
				pose proof (lemma_collinearorder _ _ _ Col_B_D_A) as (_ & _ & Col_A_B_D & _ & _).

				contradict Col_A_B_D.
				exact n_Col_A_B_D.
			}
			apply Classical_Prop.NNPP in eq_G_B.

			pose proof (lemma_equalitysymmetric _ _ eq_G_B) as eq_B_G.

			assert (~ eq G A) as neq_G_A.
			{
				intros eq_G_A.

				assert (eq B A) as eq_B_A by (rewrite eq_B_G; exact eq_G_A).

				contradict eq_B_A.
				exact neq_B_A.
			}
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_W_G_D Col_W_G_A neq_W_G) as Col_G_D_A.
			pose proof (lemma_collinearorder _ _ _ Col_G_D_A) as (_ & _ & _ & Col_G_A_D & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_A_D Col_G_A_B neq_G_A) as Col_A_D_B.
			pose proof (lemma_collinearorder _ _ _ Col_A_D_B) as (_ & _ & _ & Col_A_B_D & _).

			contradict Col_A_B_D.
			exact n_Col_A_B_D.
		}
		apply Classical_Prop.NNPP in eq_W_G.

		pose proof (lemma_equalitysymmetric _ _ eq_W_G) as eq_G_W.
		assert (BetS D G E) as BetS_D_G_E by (rewrite eq_G_W; exact BetS_D_W_E).
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_G_E) as BetS_E_G_D.

		assert (BetS G C D \/ ~ BetS G C D) as [BetS_G_C_D|nBetS_G_C_D] by (apply Classical_Prop.classic).
		{
			(* case BetS_G_C_D *)
			pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_E_G_D BetS_G_C_D) as BetS_E_G_C.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_G_C) as BetS_C_G_E.

			pose proof (lemma_s_os _ _ _ _ _ BetS_C_G_E Col_A_B_G nCol_A_B_C) as OS_C_AB_E.

			exact OS_C_AB_E.
		}
		{
			(* case nBetS_G_C_D *)
			assert (BetS G D C \/ ~ BetS G D C) as [BetS_G_D_C|nBetS_G_D_C] by (apply Classical_Prop.classic).
			{
				(* case BetS_G_D_C *)
				pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_E_G_D BetS_G_D_C) as BetS_E_G_C.
				pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_G_C) as BetS_C_G_E.

				pose proof (lemma_s_os _ _ _ _ _ BetS_C_G_E Col_A_B_G nCol_A_B_C) as OS_C_AB_E.

				exact OS_C_AB_E.
			}
			{
				(* case nBetS_G_D_C *)
				assert (~ BetS C G D) as nBetS_C_G_D.
				{
					intros BetS_C_G_D.
					pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_G_D) as BetS_D_G_C.

					pose proof (lemma_outerconnectivity _ _ _ _ BetS_Q_G_C BetS_Q_G_D nBetS_G_C_D nBetS_G_D_C) as eq_C_D.

					contradict eq_C_D.
					exact neq_C_D.
				}

				(* all remaining options have been shown to be contradictory *)
				destruct Col_G_C_D as [eq_G_C|[eq_G_D|[eq_C_D|[BetS_C_G_D|[BetS_G_C_D|BetS_G_D_C]]]]].
				{
					(* case eq_G_C *)
					pose proof (lemma_equalitysymmetric _ _ eq_G_C) as eq_C_G.
					assert (Col A B C) as Col_A_B_C by (rewrite eq_C_G; exact Col_A_B_G).

					contradict Col_A_B_C.
					exact n_Col_A_B_C.
				}
				{
					(* case eq_G_D *)
					pose proof (lemma_equalitysymmetric _ _ eq_G_D) as eq_D_G.
					assert (Col A B D) as Col_A_B_D by (rewrite eq_D_G; exact Col_A_B_G).

					contradict Col_A_B_D.
					exact n_Col_A_B_D.
				}
				{
					(* case eq_C_D *)
					contradict eq_C_D.
					exact neq_C_D.
				}
				{
					(* case BetS_C_G_D *)
					contradict BetS_C_G_D.
					exact nBetS_C_G_D.
				}
				{
					(* case BetS_G_C_D *)
					contradict BetS_G_C_D.
					exact nBetS_G_C_D.
				}
				{
					(* case BetS_G_D_C *)
					contradict BetS_G_D_C.
					exact nBetS_G_D_C.
				}
			}
		}
	}
	{
		(* case n_Col_E_D_G *)
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_E_D_G) as nCol_E_D_G.

		assert (~ Col E C G) as n_Col_E_C_G.
		{
			intros Col_E_C_G.
			pose proof (lemma_collinearorder _ _ _ Col_E_C_G) as (_ & Col_C_G_E & _ & _ & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_G_D Col_C_G_E neq_C_G) as Col_G_D_E.
			pose proof (lemma_collinearorder _ _ _ Col_G_D_E) as (_ & _ & _ & _ & Col_E_D_G).

			contradict Col_E_D_G.
			exact n_Col_E_D_G.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_E_C_G) as nCol_E_C_G.
		pose proof (lemma_NCorder _ _ _ nCol_E_C_G) as (nCol_C_E_G & nCol_C_G_E & nCol_G_E_C & nCol_E_G_C & nCol_G_C_E).

		assert (BetS G C D \/ ~ BetS G C D) as [BetS_G_C_D|nBetS_G_C_D] by (apply Classical_Prop.classic).
		{
			(* case BetS_G_C_D *)
			pose proof (
				lemma_otherside_betweenness_PABC_RQP_QABC
				_ _ _ _ _ _
				OS_D_AB_E
				BetS_G_C_D
				nCol_E_D_G
				Col_A_B_G
			) as OS_C_AB_E.
			exact OS_C_AB_E.
		}
		{
			(* case nBetS_G_C_D *)
			assert (~ ~ BetS G D C) as BetS_G_D_C.
			{
				intros nBetS_G_D_C.

				pose proof (
					lemma_outerconnectivity
					_ _ _ _
					BetS_Q_G_C BetS_Q_G_D 
					nBetS_G_C_D nBetS_G_D_C
				) as eq_C_D.

				contradict eq_C_D.
				exact neq_C_D.
			}
			apply Classical_Prop.NNPP in BetS_G_D_C.

			pose proof (
				lemma_otherside_betweenness_PABC_RPQ_QABC
				_ _ _ _ _ _
				OS_D_AB_E
				BetS_G_D_C 
				nCol_G_C_E 
				Col_A_B_G
			) as OS_C_AB_E.
			exact OS_C_AB_E.
		}
	}
Qed.


Lemma lemma_planeseparation_nCol_C_Q_D : 
	forall A B C D E Q G H,
	OS D A B E ->
	Col A B G ->
	Col A B H ->
	BetS C G Q ->
	BetS D H Q ->
	nCol A B C ->
	nCol A B D ->
	nCol C Q D ->
	neq C D ->
	OS C A B E.
Proof.
	intros A B C D E Q G H.
	intros OS_D_AB_E.
	intros Col_A_B_G.
	intros Col_A_B_H.
	intros BetS_C_G_Q.
	intros BetS_D_H_Q.
	intros nCol_A_B_C.
	intros nCol_A_B_D.
	intros nCol_C_Q_D.
	intros neq_C_D.

	assert (OS_D_AB_E2 := OS_D_AB_E).
	destruct OS_D_AB_E2 as (W & BetS_D_W_E & Col_A_B_W & _).

	pose proof (lemma_betweennotequal _ _ _ BetS_D_W_E) as (neq_W_E & neq_D_W & neq_D_E).
	assert (Col D W E) as Col_D_W_E by (unfold Col; one_of_disjunct BetS_D_W_E).
	pose proof (lemma_collinearorder _ _ _ Col_D_W_E) as (Col_W_D_E & Col_W_E_D & Col_E_D_W & Col_D_E_W & Col_E_W_D).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_W_E) as BetS_E_W_D.
	pose proof (lemma_collinearorder _ _ _ Col_A_B_W) as (Col_B_A_W & Col_B_W_A & Col_W_A_B & Col_A_W_B & Col_W_B_A).

	pose proof (lemma_collinearorder _ _ _ Col_A_B_G) as (Col_B_A_G & Col_B_G_A & Col_G_A_B & Col_A_G_B & Col_G_B_A).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_H) as (Col_B_A_H & Col_B_H_A & Col_H_A_B & Col_A_H_B & Col_H_B_A).

	pose proof (lemma_betweennotequal _ _ _ BetS_C_G_Q) as (neq_G_Q & neq_C_G & neq_C_Q).
	pose proof (lemma_betweennotequal _ _ _ BetS_D_H_Q) as (neq_H_Q & neq_D_H & neq_D_Q).
	assert (Col C G Q) as Col_C_G_Q by (unfold Col; one_of_disjunct BetS_C_G_Q).
	assert (Col D H Q) as Col_D_H_Q by (unfold Col; one_of_disjunct BetS_D_H_Q).
	pose proof (lemma_collinearorder _ _ _ Col_C_G_Q) as (Col_G_C_Q & Col_G_Q_C & Col_Q_C_G & Col_C_Q_G & Col_Q_G_C).
	pose proof (lemma_collinearorder _ _ _ Col_D_H_Q) as (Col_H_D_Q & Col_H_Q_D & Col_Q_D_H & Col_D_Q_H & Col_Q_H_D).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_G_Q) as BetS_Q_G_C.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_H_Q) as BetS_Q_H_D.

	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_D) as (_ & neq_B_D & neq_A_D & _ & neq_D_B & neq_D_A).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_D) as (nCol_B_A_D & nCol_B_D_A & nCol_D_A_B & nCol_A_D_B & nCol_D_B_A).

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_D) as n_Col_A_B_D.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_C_A_B) as n_Col_C_A_B.

	pose proof (lemma_inequalitysymmetric _ _ neq_C_G) as neq_G_C.
	pose proof (lemma_inequalitysymmetric _ _ neq_C_Q) as neq_Q_C.
	pose proof (lemma_inequalitysymmetric _ _ neq_D_E) as neq_E_D.
	pose proof (lemma_inequalitysymmetric _ _ neq_D_H) as neq_H_D.
	pose proof (lemma_inequalitysymmetric _ _ neq_D_Q) as neq_Q_D.
	pose proof (lemma_inequalitysymmetric _ _ neq_D_W) as neq_W_D.
	pose proof (lemma_inequalitysymmetric _ _ neq_H_Q) as neq_Q_H.
	pose proof (lemma_inequalitysymmetric _ _ neq_W_E) as neq_E_W.

	pose proof (lemma_NCorder _ _ _ nCol_C_Q_D) as (nCol_Q_C_D & nCol_Q_D_C & nCol_D_C_Q & nCol_C_D_Q & nCol_D_Q_C).
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_Q_C_D) as n_Col_Q_C_D.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_C_Q_D) as n_Col_C_Q_D.

	pose proof (
		postulate_Pasch_inner
		C D Q G H
		BetS_C_G_Q BetS_D_H_Q
		nCol_C_Q_D
	) as (F & BetS_C_F_H & BetS_D_F_G).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_F_H) as BetS_H_F_C.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_F_G) as BetS_G_F_D.
	pose proof (lemma_betweennotequal _ _ _ BetS_C_F_H) as (neq_F_H & neq_C_F & neq_C_H).
	pose proof (lemma_betweennotequal _ _ _ BetS_D_F_G) as (feq_F_G & neq_D_F & neq_D_G).

	pose proof (lemma_inequalitysymmetric _ _ neq_C_H) as neq_H_C.
	pose proof (lemma_inequalitysymmetric _ _ neq_D_F) as neq_F_D.

	assert (Col C F H) as Col_C_F_H by (unfold Col; one_of_disjunct BetS_C_F_H).
	pose proof (lemma_collinearorder _ _ _ Col_C_F_H) as (Col_F_C_H & Col_F_H_C & Col_H_C_F & Col_C_H_F & Col_H_F_C).
	assert (Col G F D) as Col_G_F_D by (unfold Col; one_of_disjunct BetS_G_F_D).
	pose proof (lemma_collinearorder _ _ _ Col_G_F_D) as (Col_F_G_D & Col_F_D_G & Col_D_G_F & Col_G_D_F & Col_D_F_G).

	assert (~ eq G H) as neq_G_H.
	{
		intros eq_G_H.

		assert (Col_Q_H_C := Col_Q_G_C).
		replace G with H in Col_Q_H_C.

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_H_D Col_Q_H_C neq_Q_H) as Col_H_D_C.

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_D_C Col_H_D_Q neq_H_D) as Col_D_C_Q.
		pose proof (lemma_collinearorder _ _ _ Col_D_C_Q) as (_ & Col_C_Q_D & _ & _ & _).

		contradict Col_C_Q_D.
		exact n_Col_C_Q_D.
	}

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_G Col_A_B_W neq_A_B) as Col_B_G_W.
	pose proof (lemma_collinearorder _ _ _ Col_B_G_W) as (_ & _ & Col_W_B_G & _ & _).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_H Col_A_B_G neq_A_B) as Col_B_H_G.
	pose proof (lemma_collinearorder _ _ _ Col_B_H_G) as (_ & Col_H_G_B & _ & _ & _).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_H Col_B_A_G neq_B_A) as Col_A_H_G.
	pose proof (lemma_collinearorder _ _ _ Col_A_H_G) as (_ & Col_H_G_A & _ & _ & _).

	pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_A_B Col_A_B_G Col_A_B_H Col_A_B_W) as Col_G_H_W.
	pose proof (lemma_collinearorder _ _ _ Col_G_H_W) as (Col_H_G_W & Col_H_W_G & Col_W_G_H & Col_G_W_H & Col_W_H_G).

	assert (Col E D G \/ ~ Col E D G) as [Col_E_D_G|n_Col_E_D_G] by (apply Classical_Prop.classic).
	{
		(* case Col_E_D_G *)
		assert (~ neq W G) as eq_W_G.
		{
			intros neq_W_G.

			pose proof (lemma_inequalitysymmetric _ _ neq_W_G) as neq_G_W.

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_D_G Col_E_D_W neq_E_D) as Col_D_G_W.
			pose proof (lemma_collinearorder _ _ _ Col_D_G_W) as (_ & Col_G_W_D & _ & _ & _).

			assert (eq B B) as eq_B_B by (reflexivity).
			assert (Col A B B) as Col_A_B_B by (unfold Col; one_of_disjunct eq_B_B).

			pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_A_B Col_A_B_G Col_A_B_W Col_A_B_B) as Col_G_W_B.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_W_D Col_G_W_B neq_G_W) as Col_W_D_B.

			assert (eq A A) as eq_A_A by (reflexivity).
			assert (Col B A A) as Col_B_A_A by (unfold Col; one_of_disjunct eq_A_A).
			pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_B_A Col_B_A_G Col_B_A_W Col_B_A_A) as Col_G_W_A.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_W_D Col_G_W_A neq_G_W) as Col_W_D_A.

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_W_D_B Col_W_D_A neq_W_D) as Col_D_B_A.
			pose proof (lemma_collinearorder _ _ _ Col_D_B_A) as (_ & _ & _ & _ & Col_A_B_D).

			contradict Col_A_B_D.
			exact n_Col_A_B_D.
		}
		apply Classical_Prop.NNPP in eq_W_G.

		assert (BetS_D_G_E := BetS_D_W_E).
		replace W with G in BetS_D_G_E.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_G_E) as BetS_E_G_D.
		pose proof (axiom_orderofpoints_ABD_BCD_ABC E G F D BetS_E_G_D BetS_G_F_D) as BetS_E_G_F.

		assert (~ Col H C E) as n_Col_H_C_E.
		{
			intros Col_H_C_E.
			pose proof (lemma_collinearorder _ _ _ Col_H_C_E) as (Col_C_H_E & Col_C_E_H & Col_E_H_C & Col_H_E_C & Col_E_C_H).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_C_F Col_H_C_E neq_H_C) as Col_C_F_E.
			pose proof (lemma_collinearorder _ _ _ Col_C_F_E) as (_ & _ & _ & _ & Col_E_F_C).

			pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_D_F_G BetS_D_G_E) as BetS_D_F_E.
			pose proof (lemma_betweennotequal _ _ _ BetS_D_F_E) as (neq_F_E & _ & _).
			pose proof (lemma_inequalitysymmetric _ _ neq_F_E) as neq_E_F.

			assert (Col D F E) as Col_D_F_E by (unfold Col; one_of_disjunct BetS_D_F_E).
			pose proof (lemma_collinearorder _ _ _ Col_D_F_E) as (_ & _ & _ & _ & Col_E_F_D).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_F_C Col_E_F_D neq_E_F) as Col_F_C_D.
			pose proof (lemma_collinearorder _ _ _ Col_F_C_D) as (_ & _ & _ & Col_F_D_C & _).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_F_D_C Col_F_D_G neq_F_D) as Col_D_C_G.
			pose proof (lemma_collinearorder _ _ _ Col_D_C_G) as (_ & _ & _ & _ & Col_G_C_D).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_C_D Col_G_C_Q neq_G_C) as Col_C_D_Q.
			pose proof (lemma_collinearorder _ _ _ Col_C_D_Q) as (_ & _ & Col_Q_C_D & _ & _).

			contradict Col_Q_C_D.
			exact n_Col_Q_C_D.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_H_C_E) as nCol_H_C_E.

		pose proof (
			postulate_Pasch_outer
			E H F G C
			BetS_E_G_F BetS_H_F_C
			nCol_H_C_E
		) as (M & BetS_E_M_C & BetS_H_G_M).

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_M_C) as BetS_C_M_E.
		pose proof (lemma_betweennotequal _ _ _ BetS_H_G_M) as (_ & neq_H_G & _).

		assert (Col H G M) as Col_H_G_M by (unfold Col; one_of_disjunct BetS_H_G_M).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_G_M Col_H_G_B neq_H_G) as Col_G_M_B.
		pose proof (lemma_collinearorder _ _ _ Col_G_M_B) as (_ & _ & _ & Col_G_B_M & _).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_G_A Col_H_G_M neq_H_G) as Col_G_A_M.

		assert (Col A B M) as Col_A_B_M.
		assert (eq B G \/ neq B G) as [eq_B_G|neq_B_G] by (apply Classical_Prop.classic).
		{
			(* case eq_B_G *)

			assert (Col B A M) as Col_B_A_M by (rewrite eq_B_G; exact Col_G_A_M).
			pose proof (lemma_collinearorder _ _ _ Col_B_A_M) as (Col_A_B_M & _ & _ & _ & _).

			exact Col_A_B_M.
		}
		{
			(* case neq_B_G *)
			pose proof (lemma_inequalitysymmetric _ _ neq_B_G) as neq_G_B.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_B_M Col_G_B_A neq_G_B) as Col_B_M_A.
			pose proof (lemma_collinearorder _ _ _ Col_B_M_A) as (_ & _ & Col_A_B_M & _ & _).

			exact Col_A_B_M.
		}
		pose proof (lemma_s_os
			_ _ _ _ _
			BetS_C_M_E
			Col_A_B_M
			nCol_A_B_C
		) as OS_C_AB_E.

		exact OS_C_AB_E.
	}
	{
		(* case nCol_E_D_G *)
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_E_D_G) as nCol_E_D_G.
		pose proof (lemma_NCorder _ _ _ nCol_E_D_G) as (nCol_D_E_G & nCol_D_G_E & nCol_G_E_D & nCol_E_G_D & nCol_G_D_E).

		assert (~ eq G W) as neq_G_W.
		{
			intros eq_G_W.
			assert (Col_D_G_E := Col_D_W_E).
			replace W with G in Col_D_G_E.
			pose proof (lemma_collinearorder _ _ _ Col_D_G_E) as (_ & _ & Col_E_D_G & _ & _).

			contradict Col_E_D_G.
			exact n_Col_E_D_G.
		}

		pose proof (
			lemma_otherside_betweenness_PABC_RQP_QABC
			_ _ _ _ _ _
			OS_D_AB_E
			BetS_G_F_D
			nCol_E_D_G
			Col_A_B_G
		) as OS_F_AB_E.

		assert (~ Col H C E \/ ~ ~ Col H C E) as [n_Col_H_C_E|Col_H_C_E] by (apply Classical_Prop.classic).
		{
			(* case nCol_H_C_E *)
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_H_C_E) as nCol_H_C_E.
			pose proof (
				lemma_otherside_betweenness_PABC_RPQ_QABC
				_ _ _ _ _ _
				OS_F_AB_E
				BetS_H_F_C
				nCol_H_C_E
				Col_A_B_H
			) as OS_C_AB_E.

			exact OS_C_AB_E.
		}

		(* case Col_H_C_E *)
		apply Classical_Prop.NNPP in Col_H_C_E.
		pose proof (lemma_collinearorder _ _ _ Col_H_C_E) as (Col_C_H_E & Col_C_E_H & Col_E_H_C & Col_H_E_C & Col_E_C_H).

		pose proof (
			postulate_Pasch_inner
			E G D W F
			BetS_E_W_D
			BetS_G_F_D
			nCol_E_D_G
		) as (J & BetS_E_J_F & BetS_G_J_W).
		pose proof (lemma_betweennotequal _ _ _ BetS_E_J_F) as (_ & _ & neq_E_F).
		pose proof (lemma_inequalitysymmetric _ _ neq_E_F) as neq_F_E.

		assert (Col G J W) as Col_G_J_W by (unfold Col; one_of_disjunct BetS_G_J_W).
		assert (Col E F J) as Col_E_F_J by (unfold Col; one_of_disjunct BetS_E_J_F).

		pose proof (lemma_collinearorder _ _ _ Col_G_J_W) as (_ & _ & _ & Col_G_W_J & _).
		pose proof (lemma_collinearorder _ _ _ Col_E_F_J) as (Col_F_E_J & _ & _ & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_H_F Col_C_H_E neq_C_H) as Col_H_F_E.
		pose proof (lemma_collinearorder _ _ _ Col_H_F_E) as (_ & Col_F_E_H & _ & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_F_E_J Col_F_E_H neq_F_E) as Col_E_J_H.
		pose proof (lemma_collinearorder _ _ _ Col_E_J_H) as (Col_J_E_H & Col_J_H_E & Col_H_E_J & Col_E_H_J & Col_H_J_E).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_W_J Col_G_W_H neq_G_W) as Col_W_J_H.
		pose proof (lemma_collinearorder _ _ _ Col_W_J_H) as (_ & Col_J_H_W & _ & _ & _).

		assert (~ eq H W) as neq_H_W.
		{
			intros eq_H_W.

			assert (Col_D_H_E := Col_D_W_E).
			replace W with H in Col_D_H_E.

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_H_E Col_D_H_Q neq_D_H) as Col_H_E_Q.

			assert (neq_H_E := neq_W_E).
			replace W with H in neq_H_E.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_E_Q Col_H_E_C neq_H_E) as Col_E_Q_C.
			pose proof (lemma_collinearorder _ _ _ Col_E_Q_C) as (_ & _ & _ & Col_E_C_Q & _).

			assert (~ neq E C) as eq_E_C.
			{
				intros neq_E_C.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_C_Q Col_E_C_H neq_E_C) as Col_C_Q_H.
				pose proof (lemma_collinearorder _ _ _ Col_C_Q_H) as (_ & _ & _ & _ & Col_H_Q_C).

				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_Q_C Col_H_Q_D neq_H_Q) as Col_Q_C_D.

				contradict Col_Q_C_D.
				exact n_Col_Q_C_D.
			}
			apply Classical_Prop.NNPP in eq_E_C.

			assert (Col_C_W_D := Col_E_W_D).
			replace E with C in Col_C_W_D.

			assert (Col_C_H_D := Col_C_W_D).
			replace W with H in Col_C_H_D.

			pose proof (lemma_collinearorder _ _ _ Col_C_H_D) as (_ & _ & _ & _ & Col_D_H_C).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_H_C Col_D_H_Q neq_D_H) as Col_H_C_Q.
			pose proof (lemma_collinearorder _ _ _ Col_H_C_Q) as (_ & _ & _ & Col_H_Q_C & _).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_Q_C Col_H_Q_D neq_H_Q) as Col_Q_C_D.
			pose proof (lemma_collinearorder _ _ _ Col_Q_C_D) as (Col_C_Q_D & _ & _ & _ & _).

			contradict Col_C_Q_D.
			exact n_Col_C_Q_D.
		}

		assert (~ neq J H) as eq_J_H.
		{
			intros neq_J_H.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_J_H_E Col_J_H_W neq_J_H) as Col_H_E_W.
			pose proof (lemma_collinearorder _ _ _ Col_H_E_W) as (_ & _ & _ & Col_H_W_E & _).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_W_E Col_H_W_G neq_H_W) as Col_W_E_G.

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_W_E_G Col_W_E_D neq_W_E) as Col_E_G_D.
			pose proof (lemma_collinearorder _ _ _ Col_E_G_D) as (_ & _ & _ & Col_E_D_G & _).

			contradict Col_E_D_G.
			exact n_Col_E_D_G.
		}
		apply Classical_Prop.NNPP in eq_J_H.

		assert (BetS_E_H_F := BetS_E_J_F).
		replace J with H in BetS_E_H_F.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_H_F) as BetS_F_H_E.
		pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_C_F_H BetS_F_H_E) as BetS_C_H_E.

		pose proof (
			lemma_s_os
			_ _ _ _ _
			BetS_C_H_E
			Col_A_B_H
			nCol_A_B_C
		
		) as OS_C_AB_E.

		exact OS_C_AB_E.
	}

Qed.

Lemma lemma_planeseparation : 
	forall A B C D E,
	SS C D A B ->
	OS D A B E ->
	OS C A B E.
Proof.
	intros A B C D E.
	intros SS_C_D_AB.
	intros OS_D_AB_E.

	destruct SS_C_D_AB as (Q & G & H & Col_A_B_G & Col_A_B_H & BetS_C_G_Q & BetS_D_H_Q & nCol_A_B_C & nCol_A_B_D).

	assert (eq C D \/ neq C D) as [eq_C_D|neq_C_D] by (apply Classical_Prop.classic).
	{
		(* case eq_C_D *)
		assert (OS C A B E) as OS_C_AB_E by (rewrite eq_C_D; exact OS_D_AB_E).

		exact OS_C_AB_E.
	}

	(* case neq_C_D *)
	assert (Col C Q D \/ ~ Col C Q D) as [Col_C_Q_D|n_Col_C_Q_D] by (apply Classical_Prop.classic).
	{
		(* case Col_C_Q_D *)
		pose proof (
			lemma_planeseparation_Col_C_Q_D
			A B C D E Q G H
			OS_D_AB_E
			Col_A_B_G
			Col_A_B_H
			BetS_C_G_Q
			BetS_D_H_Q
			nCol_A_B_C
			nCol_A_B_D
			Col_C_Q_D
			neq_C_D
		) as OS_C_AB_E.

		exact OS_C_AB_E.
	}
	{
		(* case n_Col_C_Q_D *)
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_C_Q_D) as nCol_C_Q_D.

		pose proof (
			lemma_planeseparation_nCol_C_Q_D
			A B C D E Q G H
			OS_D_AB_E
			Col_A_B_G
			Col_A_B_H
			BetS_C_G_Q
			BetS_D_H_Q
			nCol_A_B_C
			nCol_A_B_D
			nCol_C_Q_D
			neq_C_D
		) as OS_C_AB_E.

		exact OS_C_AB_E.
	}
Qed.

End Euclid.
