Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_angledistinct.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence_smaller.
Require Import ProofCheckingEuclid.lemma_angletrichotomy.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_equalanglesflip.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_assert.
Require Import ProofCheckingEuclid.lemma_onray_orderofpoints_any.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_conga.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_ss.
Require Import ProofCheckingEuclid.lemma_s_supp.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.
Require Import ProofCheckingEuclid.lemma_supplements_conga.
Require Import ProofCheckingEuclid.proposition_16.
Require Import ProofCheckingEuclid.lemma_equalanglesNC.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_par :
	forall A B C D U V u v X,
	neq A B ->
	neq C D ->
	Col A B U ->
	Col A B V ->
	neq U V ->
	Col C D u ->
	Col C D v ->
	neq u v ->
	~ Meet A B C D ->
	BetS U X v ->
	BetS u X V ->
	Par A B C D.
Proof.
	intros A B C D U V u v X.
	intros neq_A_B.
	intros neq_C_D.
	intros Col_A_B_U.
	intros Col_A_B_V.
	intros neq_U_V.
	intros Col_C_D_u.
	intros Col_C_D_v.
	intros neq_u_v.
	intros n_Meet_A_B_C_D.
	intros BetS_U_X_v.
	intros BetS_u_X_V.


	unfold Par.
	exists U,V,u,v,X.
	split.
	exact neq_A_B.
	split.
	exact neq_C_D.
	split.
	exact Col_A_B_U.
	split.
	exact Col_A_B_V.
	split.
	exact neq_U_V.
	split.
	exact Col_C_D_u.
	split.
	exact Col_C_D_v.
	split.
	exact neq_u_v.
	split.
	exact n_Meet_A_B_C_D.
	split.
	exact BetS_U_X_v.
	exact BetS_u_X_V.
Qed.


Lemma proposition_27 :
	forall A B C D E F,
	BetS A E B ->
	BetS C F D ->
	CongA A E F E F D ->
	OS A E F D ->
	Par A B C D.
Proof.
	intros A B C D E F.
	intros BetS_A_E_B.
	intros BetS_C_F_D.
	intros CongA_A_E_F_E_F_D.
	intros OS_A_E_F_D.

	pose proof (lemma_betweennotequal _ _ _ BetS_A_E_B) as (_ & _ & neq_A_B).
	pose proof (lemma_betweennotequal _ _ _ BetS_C_F_D) as (_ & _ & neq_C_D).

	assert (OS_A_E_F_D2 := OS_A_E_F_D).
	destruct OS_A_E_F_D2 as (H & BetS_A_H_D & Col_E_F_H & nCol_E_F_A).
	pose proof (lemma_s_col_BetS_A_B_C A E B BetS_A_E_B) as Col_A_E_B.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_E_B) as (_ & neq_A_E & _).
	pose proof (lemma_s_col_BetS_A_B_C C F D BetS_C_F_D) as Col_C_F_D.
	pose proof (lemma_betweennotequal _ _ _ BetS_C_F_D) as (neq_F_D & _ & _).
	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_A_E_F_E_F_D) as CongA_E_F_D_A_E_F.
	pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_A_E_F_E_F_D) as nCol_E_F_D.

	pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_E_F_D_A_E_F) as (neq_E_F & _ & _ & _ & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_E_F) as neq_F_E.

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_E_F_A) as n_Col_E_F_A.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_E_F_D) as n_Col_E_F_D.

	assert (~ Meet A B C D) as n_Meet_A_B_C_D.
	{
		intro Meet_A_B_C_D.

		assert (Meet_A_B_C_D2 := Meet_A_B_C_D).
		destruct Meet_A_B_C_D2 as (G & _ & _ & Col_A_B_G & Col_C_D_G).
		pose proof (lemma_collinearorder _ _ _ Col_A_B_G) as (Col_B_A_G & _ & _ & _ & _).
		pose proof (lemma_collinearorder _ _ _ Col_A_E_B) as (_ & _ & Col_B_A_E & _ & _).
		pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_G Col_B_A_E neq_B_A) as Col_A_G_E.
		pose proof (lemma_collinearorder _ _ _ Col_A_G_E) as (_ & _ & _ & Col_A_E_G & _).
		assert (eq F F) as eq_F_F by (reflexivity).
		pose proof (lemma_s_onray_assert_ABB E F neq_E_F) as OnRay_E_F_F.
		pose proof (lemma_s_supp _ _ _ _ _ OnRay_E_F_F BetS_A_E_B) as Supp_A_E_F_F_B.
		assert (eq E E) as eq_E_E by (reflexivity).
		pose proof (lemma_s_onray_assert_ABB F E neq_F_E) as OnRay_F_E_E.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_F_D) as BetS_D_F_C.
		pose proof (lemma_s_supp _ _ _ _ _ OnRay_F_E_E BetS_D_F_C) as Supp_D_F_E_E_C.
		pose proof (lemma_ABCequalsCBA _ _ _ nCol_E_F_D) as CongA_E_F_D_D_F_E.
		pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_E_F_E_F_D CongA_E_F_D_D_F_E) as CongA_A_E_F_D_F_E.
		pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_A_E_F_D_F_E Supp_A_E_F_F_B Supp_D_F_E_E_C) as CongA_F_E_B_E_F_C.
		pose proof (lemma_equalanglesflip _ _ _ _ _ _ CongA_F_E_B_E_F_C) as CongA_B_E_F_C_F_E.

		assert (~ BetS A E G) as n_BetS_A_E_G.
		{
			intro BetS_A_E_G.
			pose proof (lemma_s_col_eq_A_C E F E eq_E_E) as Col_E_F_E.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_G) as BetS_G_E_A.
			pose proof (lemma_collinearorder _ _ _ Col_C_F_D) as (_ & _ & _ & Col_C_D_F & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_D_G Col_C_D_F neq_C_D) as Col_D_G_F.
			pose proof (lemma_collinearorder _ _ _ Col_D_G_F) as (_ & Col_G_F_D & _ & _ & _).

			assert (~ eq F G) as n_eq_F_G.
			{
				intro eq_F_G.
				assert (Col A E F) as Col_A_E_F by (rewrite eq_F_G; exact Col_A_E_G).
				pose proof (lemma_collinearorder _ _ _ Col_A_E_F) as (_ & Col_E_F_A & _ & _ & _).
				contradict Col_E_F_A.
				exact n_Col_E_F_A.
			}
			assert (neq_F_G := n_eq_F_G).


			pose proof (lemma_inequalitysymmetric _ _ neq_F_G) as neq_G_F.

			assert (~ Col E F G) as n_Col_E_F_G.
			{
				intro Col_E_F_G.
				pose proof (lemma_collinearorder _ _ _ Col_E_F_G) as (_ & _ & _ & _ & Col_G_F_E).
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_F_E Col_G_F_D neq_G_F) as Col_F_E_D.
				pose proof (lemma_collinearorder _ _ _ Col_F_E_D) as (Col_E_F_D & _ & _ & _ & _).
				contradict Col_E_F_D.
				exact n_Col_E_F_D.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_E_F_G) as nCol_E_F_G.

			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_H_D) as BetS_D_H_A.
			epose proof (lemma_s_ss D G E F A H E Col_E_F_H Col_E_F_E BetS_D_H_A BetS_G_E_A nCol_E_F_D nCol_E_F_G) as SS_D_G_E_F.
			pose proof (lemma_samesidesymmetric _ _ _ _ SS_D_G_E_F) as (SS_G_D_E_F & _ & _).
			pose proof (lemma_s_col_eq_B_C E F F eq_F_F) as Col_E_F_F.
			pose proof (lemma_s_os _ _ _ _ _ BetS_D_F_C Col_E_F_F nCol_E_F_D) as OS_D_E_F_C.
			pose proof (lemma_planeseparation _ _ _ _ _ SS_G_D_E_F OS_D_E_F_C) as OS_G_E_F_C.

			destruct OS_G_E_F_C as (R & BetS_G_R_C & Col_E_F_R & _).

			assert (~ neq F R) as n_neq_F_R.
			{
				intro neq_F_R.
				pose proof (lemma_s_col_BetS_A_B_C G R C BetS_G_R_C) as Col_G_R_C.
				pose proof (lemma_collinearorder _ _ _ Col_C_D_G) as (_ & _ & _ & Col_C_G_D & _).
				pose proof (lemma_collinearorder _ _ _ Col_G_R_C) as (_ & _ & Col_C_G_R & _ & _).
				pose proof (lemma_betweennotequal _ _ _ BetS_G_R_C) as (_ & _ & neq_G_C).
				pose proof (lemma_inequalitysymmetric _ _ neq_G_C) as neq_C_G.
				pose proof (lemma_collinearorder _ _ _ Col_C_G_R) as (Col_G_C_R & _ & _ & _ & _).
				pose proof (lemma_collinearorder _ _ _ Col_C_G_D) as (Col_G_C_D & _ & _ & _ & _).
				pose proof (lemma_inequalitysymmetric _ _ neq_F_R) as neq_R_F.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_D_F Col_C_D_G neq_C_D) as Col_D_F_G.
				pose proof (lemma_collinearorder _ _ _ Col_C_D_F) as (_ & Col_D_F_C & _ & _ & _).
				pose proof (lemma_inequalitysymmetric _ _ neq_F_D) as neq_D_F.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_F_G Col_D_F_C neq_D_F) as Col_F_G_C.
				pose proof (lemma_collinearorder _ _ _ Col_F_G_C) as (_ & _ & _ & _ & Col_C_G_F).
				pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_C_G Col_C_G_R Col_C_G_F Col_C_G_D) as Col_R_F_D.
				pose proof (lemma_collinearorder _ _ _ Col_E_F_R) as (_ & _ & _ & _ & Col_R_F_E).
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_R_F_D Col_R_F_E neq_R_F) as Col_F_D_E.
				pose proof (lemma_collinearorder _ _ _ Col_F_D_E) as (_ & _ & Col_E_F_D & _ & _).
				contradict Col_E_F_D.
				exact n_Col_E_F_D.
			}
			assert (eq_F_R := n_neq_F_R).
			apply Classical_Prop.NNPP in eq_F_R.


			assert (BetS G F C) as BetS_G_F_C by (rewrite eq_F_R; exact BetS_G_R_C).

			assert (~ Col E G F) as n_Col_E_G_F.
			{
				intro Col_E_G_F.
				pose proof (lemma_collinearorder _ _ _ Col_E_G_F) as (_ & _ & _ & Col_E_F_G & _).
				contradict Col_E_F_G.
				exact n_Col_E_F_G.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_E_G_F) as nCol_E_G_F.

			pose proof (lemma_s_triangle _ _ _ nCol_E_G_F) as Triangle_E_G_F.
			pose proof (proposition_16 _ _ _ _ Triangle_E_G_F BetS_G_F_C) as (LtA_G_E_F_E_F_C & _).
			pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_G_E_F_E_F_C CongA_F_E_B_E_F_C) as LtA_G_E_F_F_E_B.
			pose proof (lemma_s_onray _ _ _ _ BetS_A_E_G BetS_A_E_B) as OnRay_E_G_B.

			assert (~ Col G E F) as n_Col_G_E_F.
			{
				intro Col_G_E_F.
				pose proof (lemma_collinearorder _ _ _ Col_G_E_F) as (Col_E_G_F & _ & _ & _ & _).
				contradict Col_E_G_F.
				exact n_Col_E_G_F.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_G_E_F) as nCol_G_E_F.

			pose proof (lemma_equalanglesreflexive _ _ _ nCol_G_E_F) as CongA_G_E_F_G_E_F.
			pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_G_E_F_G_E_F OnRay_E_G_B OnRay_E_F_F) as CongA_G_E_F_B_E_F.

			pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_G_E_F_B_E_F) as nCol_B_E_F.

			pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_E_F) as CongA_B_E_F_F_E_B.
			pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_G_E_F_B_E_F CongA_B_E_F_F_E_B) as CongA_G_E_F_F_E_B.
			pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_G_E_F_F_E_B) as CongA_F_E_B_G_E_F.
			pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_G_E_F_F_E_B CongA_F_E_B_G_E_F) as LtA_F_E_B_F_E_B.
			pose proof (lemma_angletrichotomy _ _ _ _ _ _ LtA_F_E_B_F_E_B) as n_LtA_F_E_B_F_E_B.

			contradict LtA_F_E_B_F_E_B.
			exact n_LtA_F_E_B_F_E_B.
		}


		assert (~ OnRay E A G) as n_OnRay_E_A_G.
		{
			intro OnRay_E_A_G.
			pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_E_A_G) as OnRay_E_G_A.
			pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_E_F_D_A_E_F OnRay_E_A_G OnRay_E_F_F) as CongA_E_F_D_G_E_F.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_B) as BetS_B_E_A.

			(* assert by cases *)
			assert (BetS B E G) as BetS_B_E_G.
			pose proof (lemma_onray_orderofpoints_any _ _ _ OnRay_E_A_G) as [BetS_E_G_A | [eq_A_G | BetS_E_A_G]].
			{
				(* case BetS_E_G_A *)
				pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_B_E_A BetS_E_G_A) as BetS_B_E_G.

				exact BetS_B_E_G.
			}
			{
				(* case eq_A_G *)
				pose proof (lemma_equalitysymmetric _ _ eq_A_G) as eq_G_A.
				assert (BetS B E G) as BetS_B_E_G by (rewrite eq_G_A; exact BetS_B_E_A).

				exact BetS_B_E_G.
			}
			{
				(* case BetS_E_A_G *)
				pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_B_E_A BetS_E_A_G) as BetS_B_E_G.

				exact BetS_B_E_G.
			}
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_E_G) as BetS_G_E_B.
			pose proof (lemma_s_col_eq_A_C E F E eq_E_E) as Col_E_F_E.

			assert (~ Col E F G) as n_Col_E_F_G.
			{
				intro Col_E_F_G.
				pose proof (lemma_collinearorder _ _ _ Col_A_G_E) as (_ & Col_G_E_A & _ & _ & _).
				pose proof (lemma_collinearorder _ _ _ Col_E_F_G) as (_ & _ & Col_G_E_F & _ & _).
				pose proof (lemma_betweennotequal _ _ _ BetS_B_E_G) as (neq_E_G & _ & _).
				pose proof (lemma_inequalitysymmetric _ _ neq_E_G) as neq_G_E.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_E_A Col_G_E_F neq_G_E) as Col_E_A_F.
				pose proof (lemma_collinearorder _ _ _ Col_E_A_F) as (_ & _ & _ & Col_E_F_A & _).
				contradict Col_E_F_A.
				exact n_Col_E_F_A.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_E_F_G) as nCol_E_F_G.

			pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_E_F_E Col_E_F_E BetS_A_E_B BetS_G_E_B nCol_E_F_A nCol_E_F_G) as SS_A_G_E_F.
			pose proof (lemma_samesidesymmetric _ _ _ _ SS_A_G_E_F) as (SS_G_A_E_F & _ & _).
			pose proof (lemma_planeseparation _ _ _ _ _ SS_G_A_E_F OS_A_E_F_D) as OS_G_E_F_D.

			destruct OS_G_E_F_D as (P & BetS_G_P_D & Col_E_F_P & _).
			pose proof (lemma_s_col_BetS_A_B_C G P D BetS_G_P_D) as Col_G_P_D.

			assert (~ neq P F) as n_neq_P_F.
			{
				intro neq_P_F.
				pose proof (lemma_betweennotequal _ _ _ BetS_G_P_D) as (_ & _ & neq_G_D).
				pose proof (lemma_collinearorder _ _ _ Col_G_P_D) as (_ & _ & _ & Col_G_D_P & _).
				pose proof (lemma_collinearorder _ _ _ Col_C_F_D) as (_ & _ & _ & Col_C_D_F & _).
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_D_G Col_C_D_F neq_C_D) as Col_D_G_F.
				pose proof (lemma_collinearorder _ _ _ Col_D_G_F) as (Col_G_D_F & _ & _ & _ & _).
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_D_P Col_G_D_F neq_G_D) as Col_D_P_F.
				pose proof (lemma_collinearorder _ _ _ Col_D_P_F) as (_ & Col_P_F_D & _ & _ & _).
				pose proof (lemma_collinearorder _ _ _ Col_E_F_P) as (_ & _ & _ & _ & Col_P_F_E).
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_P_F_D Col_P_F_E neq_P_F) as Col_F_D_E.
				pose proof (lemma_collinearorder _ _ _ Col_F_D_E) as (_ & _ & Col_E_F_D & _ & _).

				contradict Col_E_F_D.
				exact n_Col_E_F_D.
			}
			assert (eq_P_F := n_neq_P_F).
			apply Classical_Prop.NNPP in eq_P_F.


			assert (BetS G F D) as BetS_G_F_D by (rewrite <- eq_P_F; exact BetS_G_P_D).

			assert (~ Col F E A) as n_Col_F_E_A.
			{
				intro Col_F_E_A.
				pose proof (lemma_collinearorder _ _ _ Col_F_E_A) as (Col_E_F_A & _ & _ & _ & _).
				contradict Col_E_F_A.
				exact n_Col_E_F_A.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_F_E_A) as nCol_F_E_A.

			pose proof (lemma_equalanglesreflexive _ _ _ nCol_F_E_A) as CongA_F_E_A_F_E_A.
			pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_F_E_A_F_E_A OnRay_E_F_F OnRay_E_A_G) as CongA_F_E_A_F_E_G.
			pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_F_E_A_F_E_G) as CongA_F_E_G_F_E_A.
			pose proof (lemma_equalanglesNC _ _ _ _ _ _ CongA_F_E_A_F_E_G) as nCol_F_E_G.
			pose proof (lemma_s_ncol_n_col _ _ _ nCol_F_E_G) as n_Col_F_E_G.

			assert (~ Col E G F) as n_Col_E_G_F.
			{
				intro Col_E_G_F.
				pose proof (lemma_collinearorder _ _ _ Col_E_G_F) as (_ & _ & Col_F_E_G & _ & _).
				contradict Col_F_E_G.
				exact n_Col_F_E_G.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_E_G_F) as nCol_E_G_F.

			pose proof (lemma_s_triangle _ _ _ nCol_E_G_F) as Triangle_E_G_F.
			pose proof (proposition_16 _ _ _ _ Triangle_E_G_F BetS_G_F_D) as (LtA_G_E_F_E_F_D & _).
			pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_G_E_F_E_F_D CongA_E_F_D_G_E_F) as LtA_E_F_D_E_F_D.
			pose proof (lemma_angletrichotomy _ _ _ _ _ _ LtA_E_F_D_E_F_D) as n_LtA_E_F_D_E_F_D.

			contradict LtA_E_F_D_E_F_D.
			exact n_LtA_E_F_D_E_F_D.
		}


		(* assert by cases *)
		assert (~ Meet A B C D) as n_Meet_A_B_C_D.
		destruct Col_A_E_G as [eq_A_E | [eq_A_G | [eq_E_G | [BetS_E_A_G | [BetS_A_E_G | BetS_A_G_E]]]]].
		{
			(* case eq_A_E *)

			contradict eq_A_E.
			exact neq_A_E.
		}
		{
			(* case eq_A_G *)

			assert (~ neq H F) as n_neq_H_F.
			{
				intro neq_H_F.
				pose proof (lemma_collinearorder _ _ _ Col_C_F_D) as (_ & _ & _ & Col_C_D_F & _).
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_D_G Col_C_D_F neq_C_D) as Col_D_G_F.
				assert (Col D A F) as Col_D_A_F by (rewrite eq_A_G; exact Col_D_G_F).
				pose proof (lemma_s_col_BetS_A_B_C A H D BetS_A_H_D) as Col_A_H_D.
				pose proof (lemma_collinearorder _ _ _ Col_A_H_D) as (_ & _ & Col_D_A_H & _ & _).
				pose proof (lemma_betweennotequal _ _ _ BetS_A_H_D) as (_ & _ & neq_A_D).
				pose proof (lemma_inequalitysymmetric _ _ neq_A_D) as neq_D_A.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_A_F Col_D_A_H neq_D_A) as Col_A_F_H.
				pose proof (lemma_collinearorder _ _ _ Col_A_F_H) as (_ & _ & _ & _ & Col_H_F_A).
				pose proof (lemma_collinearorder _ _ _ Col_E_F_H) as (_ & _ & _ & _ & Col_H_F_E).
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_F_A Col_H_F_E neq_H_F) as Col_F_A_E.
				pose proof (lemma_collinearorder _ _ _ Col_F_A_E) as (_ & _ & Col_E_F_A & _ & _).
				contradict Col_E_F_A.
				exact n_Col_E_F_A.
			}
			assert (eq_H_F := n_neq_H_F).
			apply Classical_Prop.NNPP in eq_H_F.


			assert (BetS A F D) as BetS_A_F_D by (rewrite <- eq_H_F; exact BetS_A_H_D).

			assert (~ Col E A F) as n_Col_E_A_F.
			{
				intro Col_E_A_F.
				pose proof (lemma_collinearorder _ _ _ Col_E_A_F) as (_ & _ & _ & Col_E_F_A & _).
				contradict Col_E_F_A.
				exact n_Col_E_F_A.
			}
			pose proof (lemma_s_n_col_ncol _ _ _ n_Col_E_A_F) as nCol_E_A_F.

			pose proof (lemma_s_triangle _ _ _ nCol_E_A_F) as Triangle_E_A_F.
			pose proof (proposition_16 _ _ _ _ Triangle_E_A_F BetS_A_F_D) as (LtA_A_E_F_E_F_D & _).
			pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_A_E_F_E_F_D CongA_E_F_D_A_E_F) as LtA_E_F_D_E_F_D.

			pose proof (lemma_angletrichotomy _ _ _ _ _ _ LtA_E_F_D_E_F_D) as n_LtA_E_F_D_E_F_D.
			contradict LtA_E_F_D_E_F_D.
			exact n_LtA_E_F_D_E_F_D.
		}
		{
			(* case eq_E_G *)
			assert (Col C D E) as Col_C_D_E by (rewrite eq_E_G; exact Col_C_D_G).
			pose proof (lemma_collinearorder _ _ _ Col_C_F_D) as (_ & _ & _ & Col_C_D_F & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_D_E Col_C_D_F neq_C_D) as Col_D_E_F.
			pose proof (lemma_collinearorder _ _ _ Col_D_E_F) as (_ & Col_E_F_D & _ & _ & _).

			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_F_D Col_E_F_H neq_E_F) as Col_F_D_H.
			pose proof (lemma_collinearorder _ _ _ Col_F_D_H) as (_ & Col_D_H_F & _ & _ & _).
			pose proof (lemma_s_col_BetS_A_B_C A H D BetS_A_H_D) as Col_A_H_D.
			pose proof (lemma_collinearorder _ _ _ Col_A_H_D) as (_ & _ & _ & _ & Col_D_H_A).
			pose proof (lemma_betweennotequal _ _ _ BetS_A_H_D) as (neq_H_D & _ & _).
			pose proof (lemma_inequalitysymmetric _ _ neq_H_D) as neq_D_H.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_H_F Col_D_H_A neq_D_H) as Col_H_F_A.
			pose proof (lemma_collinearorder _ _ _ Col_E_F_H) as (_ & _ & _ & _ & Col_H_F_E).

			assert (~ neq H F) as n_neq_H_F.
			{
				intro neq_H_F.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_F_A Col_H_F_E neq_H_F) as Col_F_A_E.
				pose proof (lemma_collinearorder _ _ _ Col_F_A_E) as (_ & _ & Col_E_F_A & _ & _).
				contradict Col_E_F_A.
				exact n_Col_E_F_A.
			}
			assert (eq_H_F := n_neq_H_F).
			apply Classical_Prop.NNPP in eq_H_F.


			assert (Col A F D) as Col_A_F_D by (rewrite <-eq_H_F; exact Col_A_H_D).
			pose proof (lemma_collinearorder _ _ _ Col_A_F_D) as (_ & _ & _ & _ & Col_D_F_A).
			pose proof (lemma_collinearorder _ _ _ Col_C_D_F) as (_ & Col_D_F_C & _ & _ & _).
			assert (neq D F) as neq_D_F by (rewrite <- eq_H_F; exact neq_D_H).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_F_A Col_D_F_C neq_D_F) as Col_F_A_C.
			pose proof (lemma_collinearorder _ _ _ Col_F_A_C) as (_ & _ & Col_C_F_A & _ & _).
			pose proof (lemma_collinearorder _ _ _ Col_C_D_G) as (Col_D_C_G & _ & _ & _ & _).
			pose proof (lemma_collinearorder _ _ _ Col_C_D_F) as (Col_D_C_F & _ & _ & _ & _).
			pose proof (lemma_inequalitysymmetric _ _ neq_C_D) as neq_D_C.
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_C_G Col_D_C_F neq_D_C) as Col_C_G_F.
			pose proof (lemma_collinearorder _ _ _ Col_C_G_F) as (_ & _ & _ & Col_C_F_G & _).

			assert (~ neq C F) as n_neq_C_F.
			{
				intro neq_C_F.
				pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_F_A Col_C_F_G neq_C_F) as Col_F_A_G.
				assert (Col F A E) as Col_F_A_E by (rewrite eq_E_G; exact Col_F_A_G).
				pose proof (lemma_collinearorder _ _ _ Col_F_A_E) as (_ & _ & Col_E_F_A & _ & _).
				contradict Col_E_F_A.
				exact n_Col_E_F_A.
			}
			assert (eq_C_F := n_neq_C_F).
			apply Classical_Prop.NNPP in eq_C_F.


			assert (Col A C D) as Col_A_C_D by (rewrite eq_C_F; exact Col_A_F_D).
			pose proof (lemma_collinearorder _ _ _ Col_A_C_D) as (_ & Col_C_D_A & _ & _ & _).
			assert (Col F D A) as Col_F_D_A by (rewrite <- eq_C_F; exact Col_C_D_A).
			assert (Col F D E) as Col_F_D_E by (rewrite <- eq_C_F; exact Col_C_D_E).
			pose proof (lemma_collinearorder _ _ _ Col_F_D_E) as (Col_D_F_E & _ & _ & _ & _).
			pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_F_E Col_D_F_A neq_D_F) as Col_F_E_A.
			pose proof (lemma_collinearorder _ _ _ Col_F_E_A) as (Col_E_F_A & _ & _ & _ & _).
			contradict Col_E_F_A.
			exact n_Col_E_F_A.
		}
		{
			(* case BetS_E_A_G *)
			pose proof (lemma_betweennotequal _ _ _ BetS_E_A_G) as (_ & neq_E_A & _).
			
			pose proof (lemma_s_onray_assert_bets_ABE E A G BetS_E_A_G neq_E_A) as OnRay_E_A_G.

			contradict OnRay_E_A_G.
			exact n_OnRay_E_A_G.
		}
		{
			(* case BetS_A_E_G *)
			contradict BetS_A_E_G.
			exact n_BetS_A_E_G.
		}
		{
			(* case BetS_A_G_E *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_G_E) as BetS_E_G_A.
			pose proof (lemma_betweennotequal _ _ _ BetS_E_G_A) as (_ & _ & neq_E_A).
			
			pose proof (lemma_s_onray_assert_bets_AEB E A G BetS_E_G_A neq_E_A) as OnRay_E_A_G.

			contradict OnRay_E_A_G.
			exact n_OnRay_E_A_G.
		}

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (lemma_s_col_eq_A_C A B A eq_A_A) as Col_A_B_A.
	pose proof (lemma_s_col_BetS_A_C_B A B E BetS_A_E_B) as Col_A_B_E.
	assert (eq D D) as eq_D_D by (reflexivity).
	pose proof (lemma_s_col_eq_B_C C D D eq_D_D) as Col_C_D_D.
	pose proof (lemma_s_col_BetS_A_C_B C D F BetS_C_F_D) as Col_C_D_F.
	pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_A_E_B Col_C_F_D neq_A_B neq_C_D neq_A_E neq_F_D n_Meet_A_B_C_D BetS_A_H_D Col_E_F_H) as BetS_E_H_F.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_H_F) as BetS_F_H_E.

	pose proof (lemma_s_par _ _ _ _ _ _ _ _ _ neq_A_B neq_C_D Col_A_B_A Col_A_B_E neq_A_E Col_C_D_F Col_C_D_D neq_F_D n_Meet_A_B_C_D BetS_A_H_D BetS_F_H_E) as Par_A_B_C_D.

	exact Par_A_B_C_D.
Qed.

End Euclid.
