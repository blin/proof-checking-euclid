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
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_orderofpoints_any.
Require Import ProofCheckingEuclid.lemma_onray_shared_initial_point.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_lta.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_supp.
Require Import ProofCheckingEuclid.lemma_s_triangle.
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
	intros Supp_A_B_C_D_F.
	intros Supp_a_b_c_d_f.
	intros LtA_a_b_c_A_B_C.


	destruct LtA_a_b_c_A_B_C as (P & R & Q & BetS_P_R_Q & OnRay_B_A_P & OnRay_B_C_Q & CongA_a_b_c_A_B_R).
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_a_b_c_A_B_R) as nCol_A_B_R.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_R) as n_Col_A_B_R.


	destruct Supp_A_B_C_D_F as (OnRay_B_C_D & BetS_A_B_F).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_R_Q) as BetS_Q_R_P.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_F) as BetS_F_B_A.


	(* assert by cases *)
	assert (BetS F B P) as BetS_F_B_P.
	pose proof (lemma_onray_orderofpoints_any _ _ _ OnRay_B_A_P) as [BetS_B_P_A | [eq_A_P | BetS_B_A_P]].
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

	assert (~ Col F P Q) as n_Col_F_P_Q.
	{
		intro Col_F_P_Q.
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_B_A_P) as Col_B_A_P.
		pose proof (lemma_s_col_BetS_A_B_C A B F BetS_A_B_F) as Col_A_B_F.
		pose proof (lemma_betweennotequal _ _ _ BetS_A_B_F) as (_ & neq_A_B & _).
		pose proof (lemma_collinearorder _ _ _ Col_B_A_P) as (Col_A_B_P & _ & _ & _ & _).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_F Col_A_B_P neq_A_B) as Col_B_F_P.
		pose proof (lemma_collinearorder _ _ _ Col_B_F_P) as (_ & Col_F_P_B & _ & _ & _).
		pose proof (lemma_betweennotequal _ _ _ BetS_F_B_P) as (_ & _ & neq_F_P).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_F_P_Q Col_F_P_B neq_F_P) as Col_P_Q_B.
		pose proof (lemma_collinearorder _ _ _ Col_P_Q_B) as (_ & _ & _ & Col_P_B_Q & _).
		pose proof (lemma_collinearorder _ _ _ Col_B_A_P) as (_ & _ & Col_P_B_A & _ & _).
		pose proof (lemma_betweennotequal _ _ _ BetS_F_B_P) as (neq_B_P & _ & _).
		pose proof (lemma_inequalitysymmetric _ _ neq_B_P) as neq_P_B.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_P_B_Q Col_P_B_A neq_P_B) as Col_B_Q_A.
		pose proof (lemma_s_col_BetS_A_B_C P R Q BetS_P_R_Q) as Col_P_R_Q.
		pose proof (lemma_collinearorder _ _ _ Col_P_R_Q) as (_ & _ & _ & Col_P_Q_R & _).
		pose proof (lemma_betweennotequal _ _ _ BetS_P_R_Q) as (_ & _ & neq_P_Q).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_P_Q_R Col_P_Q_B neq_P_Q) as Col_Q_R_B.
		pose proof (lemma_collinearorder _ _ _ Col_Q_R_B) as (_ & _ & _ & Col_Q_B_R & _).
		pose proof (lemma_collinearorder _ _ _ Col_B_Q_A) as (Col_Q_B_A & _ & _ & _ & _).
		pose proof (lemma_onray_strict _ _ _ OnRay_B_C_Q) as neq_B_Q.
		pose proof (lemma_inequalitysymmetric _ _ neq_B_Q) as neq_Q_B.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_B_R Col_Q_B_A neq_Q_B) as Col_B_R_A.
		pose proof (lemma_collinearorder _ _ _ Col_B_R_A) as (_ & _ & Col_A_B_R & _ & _).
		contradict Col_A_B_R.
		exact n_Col_A_B_R.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_F_P_Q) as nCol_F_P_Q.

	pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_F_B_P BetS_Q_R_P nCol_F_P_Q) as (M & BetS_F_M_R & BetS_Q_M_B).
	assert (eq R R) as eq_R_R by (reflexivity).

	assert (~ eq B R) as n_eq_B_R.
	{
		intro eq_B_R.
		pose proof (lemma_s_col_eq_B_C A B R eq_B_R) as Col_A_B_R.
		contradict Col_A_B_R.
		exact n_Col_A_B_R.
	}
	assert (neq_B_R := n_eq_B_R).


	pose proof (lemma_s_onray_assert_ABB B R neq_B_R) as OnRay_B_R_R.
	pose proof (lemma_s_supp _ _ _ _ _ OnRay_B_R_R BetS_A_B_F) as Supp_A_B_R_R_F.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_a_b_c_A_B_R) as CongA_A_B_R_a_b_c.
	pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_A_B_R_a_b_c Supp_A_B_R_R_F Supp_a_b_c_d_f) as CongA_R_B_F_d_b_f.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_F) as (neq_B_F & _ & _).
	assert (eq F F) as eq_F_F by (reflexivity).
	pose proof (lemma_s_onray_assert_ABB B F neq_B_F) as OnRay_B_F_F.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_R_B_F_d_b_f) as CongA_d_b_f_R_B_F.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_d_b_f_R_B_F) as nCol_R_B_F.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_R_B_F) as n_Col_R_B_F.


	assert (~ Col F B Q) as n_Col_F_B_Q.
	{
		intro Col_F_B_Q.
		pose proof (lemma_collinearorder _ _ _ Col_F_B_Q) as (_ & _ & _ & _ & Col_Q_B_F).
		pose proof (lemma_s_col_BetS_A_B_C Q M B BetS_Q_M_B) as Col_Q_M_B.
		pose proof (lemma_collinearorder _ _ _ Col_Q_M_B) as (_ & _ & _ & Col_Q_B_M & _).
		pose proof (lemma_betweennotequal _ _ _ BetS_Q_M_B) as (_ & _ & neq_Q_B).
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_B_F Col_Q_B_M neq_Q_B) as Col_B_F_M.
		pose proof (lemma_s_col_BetS_A_B_C F M R BetS_F_M_R) as Col_F_M_R.
		pose proof (lemma_collinearorder _ _ _ Col_B_F_M) as (_ & _ & _ & _ & Col_M_F_B).
		pose proof (lemma_collinearorder _ _ _ Col_F_M_R) as (Col_M_F_R & _ & _ & _ & _).
		pose proof (lemma_betweennotequal _ _ _ BetS_F_M_R) as (_ & neq_F_M & _).
		pose proof (lemma_inequalitysymmetric _ _ neq_F_M) as neq_M_F.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_M_F_B Col_M_F_R neq_M_F) as Col_F_B_R.
		pose proof (lemma_collinearorder _ _ _ Col_F_B_R) as (_ & _ & _ & _ & Col_R_B_F).
		contradict Col_R_B_F.
		exact n_Col_R_B_F.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_F_B_Q) as nCol_F_B_Q.

	pose proof (lemma_equalanglesreflexive _ _ _ nCol_F_B_Q) as CongA_F_B_Q_F_B_Q.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_Q_M_B) as BetS_B_M_Q.
	pose proof (lemma_betweennotequal _ _ _ BetS_B_M_Q) as (_ & neq_B_M & _).
	
	pose proof (lemma_s_onray_assert_bets_ABE B M Q BetS_B_M_Q neq_B_M) as OnRay_B_M_Q.

	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_B_M_Q) as OnRay_B_Q_M.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_F_B_Q_F_B_Q OnRay_B_F_F OnRay_B_Q_M) as CongA_F_B_Q_F_B_M.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_M_R) as BetS_R_M_F.
	pose proof (lemma_s_lta _ _ _ _ _ _ _ _ _ BetS_F_M_R OnRay_B_F_F OnRay_B_R_R CongA_F_B_Q_F_B_M) as LtA_F_B_Q_F_B_R.
	pose proof (lemma_equalanglesflip _ _ _ _ _ _ CongA_d_b_f_R_B_F) as CongA_f_b_d_F_B_R.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_f_b_d_F_B_R) as CongA_F_B_R_f_b_d.
	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_F_B_Q_F_B_R CongA_f_b_d_F_B_R) as LtA_F_B_Q_f_b_d.
	pose proof (lemma_onray_shared_initial_point _ _ _ _ OnRay_B_C_Q OnRay_B_C_D) as OnRay_B_Q_D.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_F_B_Q_F_B_Q OnRay_B_F_F OnRay_B_Q_D) as CongA_F_B_Q_F_B_D.

	assert (~ Col F B D) as n_Col_F_B_D.
	{
		intro Col_F_B_D.
		pose proof (lemma_onray_impliescollinear _ _ _ OnRay_B_Q_D) as Col_B_Q_D.
		pose proof (lemma_collinearorder _ _ _ Col_B_Q_D) as (_ & _ & Col_D_B_Q & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_F_B_D) as (_ & _ & _ & _ & Col_D_B_F).
		pose proof (lemma_onray_strict _ _ _ OnRay_B_C_D) as neq_B_D.
		pose proof (lemma_inequalitysymmetric _ _ neq_B_D) as neq_D_B.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_B_Q Col_D_B_F neq_D_B) as Col_B_Q_F.
		pose proof (lemma_collinearorder _ _ _ Col_B_Q_F) as (_ & _ & Col_F_B_Q & _ & _).
		contradict Col_F_B_Q.
		exact n_Col_F_B_Q.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_F_B_D) as nCol_F_B_D.

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_F_B_D) as CongA_F_B_D_D_B_F.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_F_B_Q_F_B_D CongA_F_B_D_D_B_F) as CongA_F_B_Q_D_B_F.
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_F_B_Q_D_B_F) as CongA_D_B_F_F_B_Q.
	pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_F_B_Q_f_b_d CongA_D_B_F_F_B_Q) as LtA_D_B_F_f_b_d.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_F_B_R_f_b_d) as nCol_f_b_d.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_f_b_d) as n_Col_f_b_d.


	assert (~ Col d b f) as n_Col_d_b_f.
	{
		intro Col_d_b_f.
		pose proof (lemma_collinearorder _ _ _ Col_d_b_f) as (_ & _ & _ & _ & Col_f_b_d).
		contradict Col_f_b_d.
		exact n_Col_f_b_d.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_d_b_f) as nCol_d_b_f.

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_d_b_f) as CongA_d_b_f_f_b_d.
	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_D_B_F_f_b_d CongA_d_b_f_f_b_d) as LtA_D_B_F_d_b_f.

	exact LtA_D_B_F_d_b_f.
Qed.

End Euclid.

