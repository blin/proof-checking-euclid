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
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_oppositeside_betweenness_PABC_RPQ_QABC.
Require Import ProofCheckingEuclid.lemma_oppositeside_betweenness_PABC_RQP_QABC.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_ss.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_sameside_onray_EFAC_BFG_EGAC :
	forall A B C E F G,
	SameSide E F A C ->
	Col A B C ->
	OnRay B F G ->
	SameSide E G A C.
Proof.
	intros A B C E F G.
	intros SameSide_E_F_A_C.
	intros Col_A_B_C.
	intros OnRay_B_F_G.


	destruct SameSide_E_F_A_C as (Q & U & V & Col_A_C_U & Col_A_C_V & BetS_E_U_Q & BetS_F_V_Q & nCol_A_C_E & nCol_A_C_F).
	pose proof (lemma_s_os _ _ _ _ _ BetS_F_V_Q Col_A_C_V nCol_A_C_F) as OppositeSide_F_A_C_Q.
	pose proof (lemma_collinearorder _ _ _ Col_A_B_C) as (_ & _ & _ & Col_A_C_B & _).

	pose proof (lemma_NCdistinct _ _ _ nCol_A_C_E) as (neq_A_C & neq_C_E & neq_A_E & neq_C_A & neq_E_C & neq_E_A).
	pose proof (lemma_NCorder _ _ _ nCol_A_C_E) as (nCol_C_A_E & nCol_C_E_A & nCol_E_A_C & nCol_A_E_C & nCol_E_C_A).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_C_F) as (_ & neq_C_F & neq_A_F & _ & neq_F_C & neq_F_A).
	pose proof (lemma_NCorder _ _ _ nCol_A_C_F) as (nCol_C_A_F & nCol_C_F_A & nCol_F_A_C & nCol_A_F_C & nCol_F_C_A).
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_C_F) as n_Col_A_C_F.

	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_B_F_G) as Col_B_F_G.
	pose proof (lemma_collinearorder _ _ _ Col_B_F_G) as (Col_F_B_G & Col_F_G_B & Col_G_B_F & Col_B_G_F & Col_G_F_B).

	assert (~ ~ OppositeSide G A C Q) as n_n_OppositeSide_G_A_C_Q.
	{
		intro n_OppositeSide_G_A_C_Q.

		assert (~ eq F G) as n_eq_F_G.
		{
			intro eq_F_G.
			
			assert (OppositeSide G A C Q) as OppositeSide_G_A_C_Q by (rewrite <- eq_F_G; exact OppositeSide_F_A_C_Q).

			contradict OppositeSide_G_A_C_Q.
			exact n_OppositeSide_G_A_C_Q.
		}
		assert (neq_F_G := n_eq_F_G).


		assert (~ eq B V) as n_eq_B_V.
		{
			intro eq_B_V.
			
			assert (BetS F B Q) as BetS_F_B_Q by (rewrite eq_B_V; exact BetS_F_V_Q).

			(* assert by cases *)
			assert (BetS G B Q) as BetS_G_B_Q.
			epose proof (lemma_onray_orderofpoints_any _ _ _ OnRay_B_F_G) as [BetS_B_G_F | [eq_F_G | BetS_B_F_G]].
			{
				(* case BetS_B_G_F *)
				pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_G_F) as BetS_F_G_B.
				pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_F_G_B BetS_F_B_Q) as BetS_G_B_Q.

				exact BetS_G_B_Q.
			}
			{
				(* case eq_F_G *)
				assert (BetS G B Q) as BetS_G_B_Q by (rewrite <- eq_F_G; exact BetS_F_B_Q).

				exact BetS_G_B_Q.
			}
			{
				(* case BetS_B_F_G *)
				pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_F_G) as BetS_G_F_B.
				pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_G_F_B BetS_F_B_Q) as BetS_G_B_Q.

				exact BetS_G_B_Q.
			}

			assert (~ Col A C G) as n_Col_A_C_G.
			{
				intro Col_A_C_G.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_C_G Col_A_C_B neq_A_C) as Col_C_G_B.
				pose proof (lemma_collinearorder _ _ _ Col_C_G_B) as (_ & Col_G_B_C & _ & _ & _).
				pose proof (lemma_onray_strict _ _ _ OnRay_B_F_G) as neq_B_G.
				pose proof (lemma_inequalitysymmetric _ _ neq_B_G) as neq_G_B.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_B_C Col_G_B_F neq_G_B) as Col_B_C_F.

				assert (~ neq B C) as n_neq_B_C.
				{
					intro neq_B_C.
					pose proof (lemma_collinearorder _ _ _ Col_A_B_C) as (_ & Col_B_C_A & _ & _ & _).
					pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_C_F Col_B_C_A neq_B_C) as Col_C_F_A.
					pose proof (lemma_collinearorder _ _ _ Col_C_F_A) as (_ & _ & Col_A_C_F & _ & _).
					contradict Col_A_C_F.
					exact n_Col_A_C_F.
				}
				assert (eq_B_C := n_neq_B_C).
				apply Classical_Prop.NNPP in eq_B_C.

				
				assert (Col A B G) as Col_A_B_G by (rewrite eq_B_C; exact Col_A_C_G).
				assert (neq A B) as neq_A_B by (rewrite eq_B_C; exact neq_A_C).

				pose proof (lemma_collinearorder _ _ _ Col_A_B_G) as (_ & _ & _ & _ & Col_G_B_A).
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_B_A Col_G_B_F neq_G_B) as Col_B_A_F.
				pose proof (lemma_collinearorder _ _ _ Col_B_A_F) as (Col_A_B_F & _ & _ & _ & _).
				
				assert (Col A C F) as Col_A_C_F by (rewrite <- eq_B_C; exact Col_A_B_F).

				contradict Col_A_C_F.
				exact n_Col_A_C_F.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_C_G) as nCol_A_C_G.

			pose proof (lemma_s_os _ _ _ _ _ BetS_G_B_Q Col_A_C_B nCol_A_C_G) as OppositeSide_G_A_C_Q.
			contradict OppositeSide_G_A_C_Q.
			exact n_OppositeSide_G_A_C_Q.
		}
		assert (neq_B_V := n_eq_B_V).


		assert (~ Col Q F B) as n_Col_Q_F_B.
		{
			intro Col_Q_F_B.
			pose proof (lemma_s_col_BetS_A_B_C F V Q BetS_F_V_Q) as Col_F_V_Q.
			pose proof (lemma_collinearorder _ _ _ Col_F_V_Q) as (_ & _ & Col_Q_F_V & _ & _).
			pose proof (lemma_betweennotequal _ _ _ BetS_F_V_Q) as (_ & _ & neq_F_Q).
			pose proof (lemma_inequalitysymmetric _ _ neq_F_Q) as neq_Q_F.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_F_B Col_Q_F_V neq_Q_F) as Col_F_B_V.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_C_B Col_A_C_V neq_A_C) as Col_C_B_V.
			pose proof (lemma_collinearorder _ _ _ Col_F_B_V) as (_ & Col_B_V_F & _ & _ & _).
			pose proof (lemma_collinearorder _ _ _ Col_C_B_V) as (_ & Col_B_V_C & _ & _ & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_V_F Col_B_V_C neq_B_V) as Col_V_F_C.
			pose proof (lemma_collinearorder _ _ _ Col_V_F_C) as (_ & _ & _ & Col_V_C_F & _).
			pose proof (lemma_collinearorder _ _ _ Col_A_C_V) as (_ & _ & _ & _ & Col_V_C_A).

			assert (~ neq V C) as n_neq_V_C.
			{
				intro neq_V_C.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_V_C_F Col_V_C_A neq_V_C) as Col_C_F_A.
				pose proof (lemma_collinearorder _ _ _ Col_C_F_A) as (_ & _ & Col_A_C_F & _ & _).
				contradict Col_A_C_F.
				exact n_Col_A_C_F.
			}
			assert (eq_V_C := n_neq_V_C).
			apply Classical_Prop.NNPP in eq_V_C.

			assert (neq A V) as neq_A_V by (rewrite eq_V_C; exact neq_A_C).

			pose proof (lemma_inequalitysymmetric _ _ neq_A_V) as neq_V_A.
			pose proof (lemma_collinearorder _ _ _ Col_A_C_B) as (Col_C_A_B & _ & _ & _ & _).
			pose proof (lemma_collinearorder _ _ _ Col_A_C_V) as (Col_C_A_V & _ & _ & _ & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_A_B Col_C_A_V neq_C_A) as Col_A_B_V.
			pose proof (lemma_collinearorder _ _ _ Col_A_B_V) as (_ & Col_B_V_A & _ & _ & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_V_F Col_B_V_A neq_B_V) as Col_V_F_A.
			pose proof (lemma_collinearorder _ _ _ Col_V_F_A) as (_ & _ & _ & Col_V_A_F & _).
			pose proof (lemma_collinearorder _ _ _ Col_A_C_V) as (_ & _ & Col_V_A_C & _ & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_V_A_F Col_V_A_C neq_V_A) as Col_A_F_C.
			pose proof (lemma_collinearorder _ _ _ Col_A_F_C) as (_ & _ & _ & Col_A_C_F & _).
			contradict Col_A_C_F.
			exact n_Col_A_C_F.
		}
		pose proof (lemma_s_n_col_ncol _ _ _ n_Col_Q_F_B) as nCol_Q_F_B.


		(* assert by cases *)
		assert (OppositeSide G A C Q) as OppositeSide_G_A_C_Q.
		epose proof (lemma_onray_orderofpoints_any _ _ _ OnRay_B_F_G) as [BetS_B_G_F | [eq_F_G | BetS_B_F_G]].
		{
			(* case BetS_B_G_F *)
			pose proof (lemma_oppositeside_betweenness_PABC_RQP_QABC _ _ _ _ _ _ OppositeSide_F_A_C_Q BetS_B_G_F nCol_Q_F_B Col_A_C_B) as OppositeSide_G_A_C_Q.

			exact OppositeSide_G_A_C_Q.
		}
		{
			(* case eq_F_G *)
			
			assert (OppositeSide G A C Q) as OppositeSide_G_A_C_Q by (rewrite <- eq_F_G; exact OppositeSide_F_A_C_Q).

			exact OppositeSide_G_A_C_Q.
		}
		{
			(* case BetS_B_F_G *)

			assert (~ Col B G Q) as n_Col_B_G_Q.
			{
				intro Col_B_G_Q.
				pose proof (lemma_betweennotequal _ _ _ BetS_B_F_G) as (_ & neq_B_F & neq_B_G).
				pose proof (lemma_inequalitysymmetric _ _ neq_B_G) as neq_G_B.
				pose proof (lemma_collinearorder _ _ _ Col_B_G_Q) as (Col_G_B_Q & _ & _ & _ & _).
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_B_F Col_G_B_Q neq_G_B) as Col_B_F_Q.
				pose proof (lemma_collinearorder _ _ _ Col_B_F_Q) as (_ & _ & _ & _ & Col_Q_F_B).
				contradict Col_Q_F_B.
				exact n_Col_Q_F_B.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_B_G_Q) as nCol_B_G_Q.

			pose proof (lemma_oppositeside_betweenness_PABC_RPQ_QABC _ _ _ _ _ _ OppositeSide_F_A_C_Q BetS_B_F_G nCol_B_G_Q Col_A_C_B) as OppositeSide_G_A_C_Q.

			exact OppositeSide_G_A_C_Q.
		}
		contradict OppositeSide_G_A_C_Q.
		exact n_OppositeSide_G_A_C_Q.
	}
	assert (OppositeSide_G_A_C_Q := n_n_OppositeSide_G_A_C_Q).
	apply Classical_Prop.NNPP in OppositeSide_G_A_C_Q.


	destruct OppositeSide_G_A_C_Q as (H & BetS_G_H_Q & Col_A_C_H & nCol_A_C_G).
	pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_A_C_U Col_A_C_H BetS_E_U_Q BetS_G_H_Q nCol_A_C_E nCol_A_C_G) as SameSide_E_G_A_C.

	exact SameSide_E_G_A_C.
Qed.

End Euclid.
