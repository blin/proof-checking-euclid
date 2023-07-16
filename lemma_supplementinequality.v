Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_LtA.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_Supp.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence_smaller.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalanglesflip.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_orderofpoints_any.
Require Import ProofCheckingEuclid.lemma_onray_shared_initial_point.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_supplements_conga.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_supplementinequality :
	forall A B C D F a b c d f,
	Supp A B C D F ->
	Supp a b c d f ->
	LtA a b c A B C ->
	LtA D B F d b f.
Proof.
	intros A B C D F a b c d f.
	intros Supp_ABC_DBF.
	intros Supp_abc_dbf.
	intros LtA_abc_ABC.

	destruct Supp_ABC_DBF as (OnRay_BC_D & BetS_A_B_F).

	pose proof (lemma_onray_strict _ _ _ OnRay_BC_D) as neq_B_D.
	pose proof (lemma_inequalitysymmetric _ _ neq_B_D) as neq_D_B.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_F) as BetS_F_B_A.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_F) as (_ & neq_A_B & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_F) as (neq_B_F & _ & _).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_B_F) as Col_A_B_F.

	destruct LtA_abc_ABC as (P & R & Q & BetS_P_R_Q & OnRay_BA_P & OnRay_BC_Q & CongA_abc_ABR).

	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_abc_ABR) as CongA_ABR_abc.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_abc_ABR) as nCol_A_B_R.
	pose proof (lemma_NCorder _ _ _ nCol_A_B_R) as (nCol_B_A_R & nCol_B_R_A & nCol_R_A_B & nCol_A_R_B & nCol_R_B_A).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_R_Q) as BetS_Q_R_P.
	pose proof (lemma_betweennotequal _ _ _ BetS_P_R_Q) as (_ & _ & neq_P_Q).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_P_R_Q) as Col_P_R_Q.
	pose proof (lemma_collinearorder _ _ _ Col_P_R_Q) as (Col_R_P_Q & Col_R_Q_P & Col_Q_P_R & Col_P_Q_R & Col_Q_R_P).

	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_BA_P) as Col_B_A_P.
	pose proof (lemma_collinearorder _ _ _ Col_B_A_P) as (Col_A_B_P & Col_A_P_B & Col_P_B_A & Col_B_P_A & Col_P_A_B).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_F Col_A_B_P neq_A_B) as Col_B_F_P.
	pose proof (lemma_collinearorder _ _ _ Col_B_F_P) as (Col_F_B_P & Col_F_P_B & Col_P_B_F & Col_B_P_F & Col_P_F_B).

	pose proof (lemma_onray_shared_initial_point _ _ _ _ OnRay_BC_Q OnRay_BC_D) as OnRay_BQ_D.
	pose proof (lemma_onray_strict _ _ _ OnRay_BC_Q) as neq_B_Q.
	pose proof (lemma_inequalitysymmetric _ _ neq_B_Q) as neq_Q_B.

	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_BQ_D) as Col_B_Q_D.
	pose proof (lemma_collinearorder _ _ _ Col_B_Q_D) as (Col_Q_B_D & Col_Q_D_B & Col_D_B_Q & Col_B_D_Q & Col_D_Q_B).


	(* assert by cases *)
	assert (BetS F B P) as BetS_F_B_P.
	pose proof (lemma_onray_orderofpoints_any _ _ _ OnRay_BA_P) as [BetS_B_P_A | [eq_A_P | BetS_B_A_P]].
	{
		(* case BetS_B_P_A *)
		pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_F_B_A BetS_B_P_A) as BetS_F_B_P.

		exact BetS_F_B_P.
	}
	{
		(* case eq_A_P *)
		assert (BetS F B P) as BetS_F_B_P by (rewrite <- eq_A_P; exact BetS_F_B_A).

		exact BetS_F_B_P.
	}
	{
		(* case BetS_B_A_P *)
		pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_F_B_A BetS_B_A_P) as BetS_F_B_P.

		exact BetS_F_B_P.
	}

	pose proof (lemma_betweennotequal _ _ _ BetS_F_B_P) as (_ & _ & neq_F_P).
	pose proof (lemma_betweennotequal _ _ _ BetS_F_B_P) as (neq_B_P & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_F_P) as neq_P_F.

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_A_R Col_B_A_P neq_B_P) as nCol_B_P_R.
	pose proof (lemma_NCdistinct _ _ _ nCol_B_P_R) as (_ & neq_P_R & neq_B_R & neq_P_B & neq_R_P & neq_R_B).
	pose proof (lemma_NCorder _ _ _ nCol_B_P_R) as (nCol_P_B_R & nCol_P_R_B & nCol_R_B_P & nCol_B_R_P & nCol_R_P_B).

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_F) as OnRay_BF_F.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_R) as OnRay_BR_R.
	pose proof (by_def_Supp _ _ _ _ _ OnRay_BR_R BetS_A_B_F) as Supp_ABR_RBF.

	pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_ABR_abc Supp_ABR_RBF Supp_abc_dbf) as CongA_RBF_dbf.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_RBF_dbf) as CongA_dbf_RBF.
	pose proof (lemma_equalanglesflip _ _ _ _ _ _ CongA_dbf_RBF) as CongA_fbd_FBR.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_fbd_FBR) as CongA_FBR_fbd.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_FBR_fbd) as nCol_f_b_d.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_dbf_RBF) as nCol_R_B_F.

	pose proof (lemma_NCorder _ _ _ nCol_f_b_d) as (nCol_b_f_d & nCol_b_d_f & nCol_d_f_b & nCol_f_d_b & nCol_d_b_f).
	pose proof (lemma_NCorder _ _ _ nCol_R_B_F) as (nCol_B_R_F & nCol_B_F_R & nCol_F_R_B & nCol_R_F_B & nCol_F_B_R).

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_d_b_f) as CongA_dbf_fbd.

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_P_R_B Col_P_R_Q neq_P_Q) as nCol_P_Q_B.
	pose proof (lemma_NCorder _ _ _ nCol_P_Q_B) as (nCol_Q_P_B & nCol_Q_B_P & nCol_B_P_Q & nCol_P_B_Q & nCol_B_Q_P).
	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_P_B_Q Col_P_B_F neq_P_F) as nCol_P_F_Q.
	pose proof (lemma_NCorder _ _ _ nCol_P_F_Q) as (nCol_F_P_Q & nCol_F_Q_P & nCol_Q_P_F & nCol_P_Q_F & nCol_Q_F_P).

	pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_F_B_P BetS_Q_R_P nCol_F_P_Q) as (M & BetS_F_M_R & BetS_Q_M_B).

	pose proof (lemma_betweennotequal _ _ _ BetS_F_M_R) as (_ & neq_F_M & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_F_M) as neq_M_F.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_F_M_R) as Col_F_M_R.
	pose proof (lemma_collinearorder _ _ _ Col_F_M_R) as (Col_M_F_R & Col_M_R_F & Col_R_F_M & Col_F_R_M & Col_R_M_F).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_Q_M_B) as BetS_B_M_Q.
	pose proof (lemma_betweennotequal _ _ _ BetS_B_M_Q) as (_ & neq_B_M & _).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_Q_M_B) as Col_Q_M_B.
	pose proof (lemma_collinearorder _ _ _ Col_Q_M_B) as (Col_M_Q_B & Col_M_B_Q & Col_B_Q_M & Col_Q_B_M & Col_B_M_Q).

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_M_Q neq_B_M) as OnRay_BM_Q.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_BM_Q) as OnRay_BQ_M.

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_F_R_B Col_F_R_M neq_F_M) as nCol_F_M_B.
	pose proof (lemma_NCorder _ _ _ nCol_F_M_B) as (nCol_M_F_B & nCol_M_B_F & nCol_B_F_M & nCol_F_B_M & nCol_B_M_F).

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_M_F Col_B_M_Q neq_B_Q) as nCol_B_Q_F.
	pose proof (lemma_NCorder _ _ _ nCol_B_Q_F) as (nCol_Q_B_F & nCol_Q_F_B & nCol_F_B_Q & nCol_B_F_Q & nCol_F_Q_B).

	pose proof (lemma_equalanglesreflexive _ _ _ nCol_F_B_Q) as CongA_FBQ_FBQ.

	pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_Q_F Col_B_Q_D neq_B_D) as nCol_B_D_F.
	pose proof (lemma_NCorder _ _ _ nCol_B_D_F) as (nCol_D_B_F & nCol_D_F_B & nCol_F_B_D & nCol_B_F_D & nCol_F_D_B).

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_F_B_D) as CongA_FBD_DBF.

	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_FBQ_FBQ OnRay_BF_F OnRay_BQ_M) as CongA_FBQ_FBM.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_FBQ_FBQ OnRay_BF_F OnRay_BQ_D) as CongA_FBQ_FBD.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_FBQ_FBD CongA_FBD_DBF) as CongA_FBQ_DBF.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_FBQ_DBF) as CongA_DBF_FBQ.

	pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_F_M_R OnRay_BF_F OnRay_BR_R CongA_FBQ_FBM) as LtA_FBQ_FBR.
	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_FBQ_FBR CongA_fbd_FBR) as LtA_FBQ_fbd.
	pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_FBQ_fbd CongA_DBF_FBQ) as LtA_DBF_fbd.

	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_DBF_fbd CongA_dbf_fbd) as LtA_DBF_dbf.

	exact LtA_DBF_dbf.
Qed.

End Euclid.
