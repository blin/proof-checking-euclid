Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_orderofpoints_any.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_oppositeside_betweenness_PABC_RPQ_QABC.
Require Import ProofCheckingEuclid.lemma_oppositeside_betweenness_PABC_RQP_QABC.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_os.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_oppositeside_onray_PABC_RQP_QABC :
	forall A B C P Q R,
	OppositeSide P A B C ->
	OnRay R Q P ->
	Col A B R ->
	OppositeSide Q A B C.
Proof.
	intros A B C P Q R.
	intros OppositeSide_P_A_B_C.
	intros OnRay_R_Q_P.
	intros Col_A_B_R.

	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_R_Q_P) as Col_R_Q_P.
	pose proof (lemma_collinearorder _ _ _ Col_R_Q_P) as (Col_Q_R_P & Col_Q_P_R & Col_P_R_Q & Col_R_P_Q & Col_P_Q_R).

	pose proof (lemma_collinearorder _ _ _ Col_A_B_R) as (Col_B_A_R & Col_B_R_A & Col_R_A_B & Col_A_R_B & Col_R_B_A).

	assert (OppositeSide_P_A_B_C2 := OppositeSide_P_A_B_C).
	destruct OppositeSide_P_A_B_C2 as (L & BetS_P_L_C & Col_A_B_L & nCol_A_B_P).

	pose proof (lemma_betweennotequal _ _ _ BetS_P_L_C) as (_ & _ & neq_P_C).
	pose proof (lemma_inequalitysymmetric _ _ neq_P_C) as neq_C_P.

	pose proof (lemma_s_col_BetS_A_C_B P C L BetS_P_L_C) as Col_P_C_L.
	pose proof (lemma_collinearorder _ _ _ Col_P_C_L) as (Col_C_P_L & Col_C_L_P & Col_L_P_C & Col_P_L_C & Col_L_C_P).

	pose proof (lemma_collinearorder _ _ _ Col_A_B_L) as (Col_B_A_L & Col_B_L_A & Col_L_A_B & Col_A_L_B & Col_L_B_A).

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_P) as n_Col_A_B_P.
	pose proof (lemma_NCorder _ _ _ nCol_A_B_P) as (nCol_B_A_P & nCol_B_P_A & nCol_P_A_B & nCol_A_P_B & nCol_P_B_A).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_P) as (neq_A_B & neq_B_P & neq_A_P & neq_B_A & neq_P_B & neq_P_A).

	(* assert by cases *)
	assert (OppositeSide Q A B C) as OppositeSide_Q_A_B_C.
	assert (Col C P R \/ ~ Col C P R) as [Col_C_P_R|n_Col_C_P_R] by (apply Classical_Prop.classic).
	{
		(* case Col_C_P_R *)

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_P_L Col_C_P_R neq_C_P) as Col_P_L_R.
		pose proof (lemma_collinearorder _ _ _ Col_P_L_R) as (Col_L_P_R & Col_L_R_P & Col_R_P_L & Col_P_R_L & Col_R_L_P).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_L Col_A_B_R neq_A_B) as Col_B_L_R.
		pose proof (lemma_collinearorder _ _ _ Col_B_L_R) as (Col_L_B_R & Col_L_R_B & Col_R_B_L & Col_B_R_L & Col_R_L_B).

		assert (~ neq L R) as n_neq_L_R.
		{
			intro neq_L_R.

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_L_R_P Col_L_R_B neq_L_R) as Col_R_P_B.
			pose proof (lemma_collinearorder _ _ _ Col_R_P_B) as (_ & _ & _ & Col_R_B_P & _).

			assert (~ neq R B) as n_neq_R_B.
			{
				intro neq_R_B.

				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_R_B_P Col_R_B_A neq_R_B) as Col_B_P_A.
				pose proof (lemma_collinearorder _ _ _ Col_B_P_A) as (_ & _ & Col_A_B_P & _ & _).

				contradict Col_A_B_P.
				exact n_Col_A_B_P.
			}
			assert (eq_R_B := n_neq_R_B).
			apply Classical_Prop.NNPP in eq_R_B.

			assert (neq R A) as neq_R_A by (rewrite eq_R_B; exact neq_B_A).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_L Col_B_A_R neq_B_A) as Col_A_L_R.
			pose proof (lemma_collinearorder _ _ _ Col_A_L_R) as (_ & Col_L_R_A & _ & _ & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_L_R_P Col_L_R_A neq_L_R) as Col_R_P_A.
			pose proof (lemma_collinearorder _ _ _ Col_R_P_A) as (_ & _ & _ & Col_R_A_P & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_R_A_P Col_R_A_B neq_R_A) as Col_A_P_B.
			pose proof (lemma_collinearorder _ _ _ Col_A_P_B) as (_ & _ & _ & Col_A_B_P & _).

			contradict Col_A_B_P.
			exact n_Col_A_B_P.
		}
		assert (eq_L_R := n_neq_L_R).
		apply Classical_Prop.NNPP in eq_L_R.


		assert (BetS P R C) as BetS_P_R_C by (rewrite <- eq_L_R; exact BetS_P_L_C).
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_R_C) as BetS_C_R_P.

		(* assert by cases *)
		assert (BetS C R Q) as BetS_C_R_Q.
		pose proof (lemma_onray_orderofpoints_any _ _ _ OnRay_R_Q_P) as [BetS_R_P_Q | [eq_Q_P | BetS_R_Q_P]].
		{
			(* case BetS_R_P_Q *)
			pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_C_R_P BetS_R_P_Q) as BetS_C_R_Q.

			exact BetS_C_R_Q.
		}
		{
			(* case eq_Q_P *)
			assert (BetS C R Q) as BetS_C_R_Q by (rewrite eq_Q_P; exact BetS_C_R_P).

			exact BetS_C_R_Q.
		}
		{
			(* case BetS_R_Q_P *)
			pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_C_R_P BetS_R_Q_P) as BetS_C_R_Q.

			exact BetS_C_R_Q.
		}

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_R_Q) as BetS_Q_R_C.
		pose proof (lemma_betweennotequal _ _ _ BetS_Q_R_C) as (_ & neq_Q_R & _).

		pose proof (lemma_s_col_BetS_A_B_C Q R C BetS_Q_R_C) as Col_Q_R_C.
		pose proof (lemma_collinearorder _ _ _ Col_Q_R_C) as (Col_R_Q_C & Col_R_C_Q & Col_C_Q_R & Col_Q_C_R & Col_C_R_Q).

		assert (~ Col A B Q) as n_Col_A_B_Q.
		{
			intro Col_A_B_Q.

			pose proof (lemma_collinearorder _ _ _ Col_A_B_Q) as (Col_B_A_Q & Col_B_Q_A & Col_Q_A_B & Col_A_Q_B & Col_Q_B_A).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_Q Col_A_B_R neq_A_B) as Col_B_Q_R.
			pose proof (lemma_collinearorder _ _ _ Col_B_Q_R) as (Col_Q_B_R & Col_Q_R_B & Col_R_B_Q & Col_B_R_Q & Col_R_Q_B).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_R_B Col_Q_R_P neq_Q_R) as Col_R_B_P.

			assert (~ neq R B) as n_neq_R_B.
			{
				intro neq_R_B.

				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_R_B_P Col_R_B_A neq_R_B) as Col_B_P_A.
				pose proof (lemma_collinearorder _ _ _ Col_B_P_A) as (_ & _ & Col_A_B_P & _ & _).

				contradict Col_A_B_P.
				exact n_Col_A_B_P.
			}
			assert (eq_R_B := n_neq_R_B).
			apply Classical_Prop.NNPP in eq_R_B.

			assert (neq R A) as neq_R_A by (rewrite eq_R_B; exact neq_B_A).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_Q Col_B_A_R neq_B_A) as Col_A_Q_R.
			pose proof (lemma_collinearorder _ _ _ Col_A_Q_R) as (Col_Q_A_R & Col_Q_R_A & Col_R_A_Q & Col_A_R_Q & Col_R_Q_A).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_R_A Col_Q_R_P neq_Q_R) as Col_R_A_P.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_R_A_P Col_R_A_B neq_R_A) as Col_A_P_B.
			pose proof (lemma_collinearorder _ _ _ Col_A_P_B) as (_ & _ & _ & Col_A_B_P & _).

			contradict Col_A_B_P.
			exact n_Col_A_B_P.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_B_Q) as nCol_A_B_Q.

		pose proof (lemma_s_os _ _ _ _ _ BetS_Q_R_C Col_A_B_R nCol_A_B_Q) as OppositeSide_Q_A_B_C.

		exact OppositeSide_Q_A_B_C.
	}
	{
		(* case n_Col_C_P_R *)
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_C_P_R) as nCol_C_P_R.
		pose proof (lemma_NCorder _ _ _ nCol_C_P_R) as (nCol_P_C_R & nCol_P_R_C & nCol_R_C_P & nCol_C_R_P & nCol_R_P_C).

		(* assert by cases *)
		assert (OppositeSide Q A B C) as OppositeSide_Q_A_B_C.
		pose proof (lemma_onray_orderofpoints_any _ _ _ OnRay_R_Q_P) as [BetS_R_P_Q | [eq_Q_P | BetS_R_Q_P]].
		{
			(* case BetS_R_P_Q *)
			pose proof (lemma_betweennotequal _ _ _ BetS_R_P_Q) as (_ & _ & neq_R_Q).

			epose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD R P C Q nCol_R_P_C Col_R_P_Q neq_R_Q) as nCol_R_Q_C.

			pose proof (lemma_oppositeside_betweenness_PABC_RPQ_QABC _ _ _ _ _ _ OppositeSide_P_A_B_C BetS_R_P_Q nCol_R_Q_C Col_A_B_R) as OppositeSide_Q_A_B_C.

			exact OppositeSide_Q_A_B_C.
		}
		{
			(* case eq_Q_P *)
			assert (OppositeSide Q A B C) as OppositeSide_Q_A_B_C by (rewrite eq_Q_P; exact OppositeSide_P_A_B_C).

			exact OppositeSide_Q_A_B_C.
		}
		{
			(* case BetS_R_Q_P *)
			pose proof (lemma_oppositeside_betweenness_PABC_RQP_QABC _ _ _ _ _ _ OppositeSide_P_A_B_C BetS_R_Q_P nCol_C_P_R Col_A_B_R) as OppositeSide_Q_A_B_C.

			exact OppositeSide_Q_A_B_C.
		}

		exact OppositeSide_Q_A_B_C.
	}

	exact OppositeSide_Q_A_B_C.
Qed.

End Euclid.
