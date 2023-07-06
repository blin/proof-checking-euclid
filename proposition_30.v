Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_30helper.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NChelper.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearbetween.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_collinearparallel.
Require Import ProofCheckingEuclid.lemma_crossimpliesopposite.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_oppositesidesymmetric.
Require Import ProofCheckingEuclid.lemma_parallelNC.
Require Import ProofCheckingEuclid.lemma_paralleldef2B.
Require Import ProofCheckingEuclid.lemma_parallelflip.
Require Import ProofCheckingEuclid.lemma_parallelsymmetric.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_B_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_isosceles.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_oncirc_radius.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_AEB.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_ss.
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.
Require Import ProofCheckingEuclid.proposition_30A.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma parnotmeet :
	forall A B C D,
	Par A B C D ->
	~ Meet A B C D.
Proof.
	intros A B C D.
	intros Par_A_B_C_D.

	destruct Par_A_B_C_D as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_A_B_C_D & _ & _).
	exact n_Meet_A_B_C_D.
Qed.

Lemma proposition_30 :
	forall A B C D E F G H K,
	Par A B E F ->
	Par C D E F ->
	BetS G H K ->
	Col A B G ->
	Col E F H ->
	Col C D K ->
	neq A G ->
	neq E H ->
	neq C K ->
	Par A B C D.
Proof.
	intros A B C D E F G H K.
	intros Par_A_B_E_F.
	intros Par_C_D_E_F.
	intros BetS_G_H_K.
	intros Col_A_B_G.
	intros Col_E_F_H.
	intros Col_C_D_K.
	intros neq_A_G.
	intros neq_E_H.
	intros neq_C_K.

	pose proof (lemma_extension A G A G neq_A_G neq_A_G) as (b & BetS_A_G_b & Cong_G_b_A_G).
	pose proof (lemma_extension E H E H neq_E_H neq_E_H) as (f & BetS_E_H_f & Cong_H_f_E_H).
	pose proof (lemma_extension C K C K neq_C_K neq_C_K) as (d & BetS_C_K_d & Cong_K_d_C_K).
	pose proof (lemma_parallelNC _ _ _ _ Par_C_D_E_F) as (nCol_C_D_E & _ & _ & _).
	pose proof (lemma_NCdistinct _ _ _ nCol_C_D_E) as (neq_C_D & _ & _ & _ & _ & _).
	pose proof (lemma_s_col_BetS_A_B_C A G b BetS_A_G_b) as Col_A_G_b.
	pose proof (lemma_collinearorder _ _ _ Col_A_G_b) as (Col_G_A_b & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_G) as (_ & _ & Col_G_A_B & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_G) as neq_G_A.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_G_A_b Col_G_A_B neq_G_A) as Col_A_b_B.
	pose proof (lemma_collinearorder _ _ _ Col_A_b_B) as (_ & _ & Col_B_A_b & _ & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_A_B_E_F) as Par_E_F_A_B.
	pose proof (lemma_parallelflip _ _ _ _ Par_E_F_A_B) as (_ & Par_E_F_B_A & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_G_b) as (_ & _ & neq_A_b).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_b) as neq_b_A.
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_E_F_B_A Col_B_A_b neq_b_A) as Par_E_F_b_A.
	pose proof (lemma_parallelflip _ _ _ _ Par_E_F_b_A) as (_ & Par_E_F_A_b & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_E_F_A_b) as Par_A_b_E_F.
	pose proof (lemma_s_col_BetS_A_B_C E H f BetS_E_H_f) as Col_E_H_f.
	pose proof (lemma_collinearorder _ _ _ Col_E_H_f) as (Col_H_E_f & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_E_F_H) as (_ & _ & Col_H_E_F & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_E_H) as neq_H_E.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_E_f Col_H_E_F neq_H_E) as Col_E_f_F.
	pose proof (lemma_collinearorder _ _ _ Col_E_f_F) as (_ & _ & Col_F_E_f & _ & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_H_f) as (_ & _ & neq_E_f).
	pose proof (lemma_inequalitysymmetric _ _ neq_E_f) as neq_f_E.
	pose proof (lemma_parallelflip _ _ _ _ Par_A_b_E_F) as (_ & Par_A_b_F_E & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_A_b_F_E Col_F_E_f neq_f_E) as Par_A_b_f_E.
	pose proof (lemma_parallelflip _ _ _ _ Par_A_b_f_E) as (_ & Par_A_b_E_f & _).
	pose proof (lemma_s_col_BetS_A_B_C C K d BetS_C_K_d) as Col_C_K_d.
	pose proof (lemma_collinearorder _ _ _ Col_C_K_d) as (Col_K_C_d & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_D_K) as (_ & _ & Col_K_C_D & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_C_K) as neq_K_C.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_K_C_d Col_K_C_D neq_K_C) as Col_C_d_D.
	pose proof (lemma_collinearorder _ _ _ Col_C_d_D) as (_ & _ & Col_D_C_d & _ & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_C_D_E_F) as Par_E_F_C_D.
	pose proof (lemma_parallelflip _ _ _ _ Par_E_F_C_D) as (_ & Par_E_F_D_C & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_C_K_d) as (_ & _ & neq_C_d).
	pose proof (lemma_inequalitysymmetric _ _ neq_C_d) as neq_d_C.
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_E_F_D_C Col_D_C_d neq_d_C) as Par_E_F_d_C.
	pose proof (lemma_parallelflip _ _ _ _ Par_E_F_d_C) as (_ & Par_E_F_C_d & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_E_F_C_d) as Par_C_d_E_F.
	pose proof (lemma_parallelflip _ _ _ _ Par_C_d_E_F) as (_ & Par_C_d_F_E & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_C_d_F_E Col_F_E_f neq_f_E) as Par_C_d_f_E.
	pose proof (lemma_parallelflip _ _ _ _ Par_C_d_f_E) as (_ & Par_C_d_E_f & _).
	assert (eq H H) as eq_H_H by (reflexivity).
	pose proof (lemma_s_col_eq_B_C E H H eq_H_H) as Col_E_H_H.
	pose proof (lemma_collinearorder _ _ _ Col_G_A_b) as (_ & Col_A_b_G & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_H_E_f) as (_ & Col_E_f_H & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_E_f_H) as (Col_f_E_H & _ & _ & _ & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_A_b_f_E Col_f_E_H neq_H_E) as Par_A_b_H_E.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_A_b_H_E) as Par_H_E_A_b.
	pose proof (lemma_parallelflip _ _ _ _ Par_H_E_A_b) as (_ & _ & Par_E_H_b_A).
	pose proof (lemma_collinearorder _ _ _ Col_A_b_G) as (Col_b_A_G & _ & _ & _ & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_E_H_b_A Col_b_A_G neq_G_A) as Par_E_H_G_A.
	pose proof (lemma_parallelflip _ _ _ _ Par_E_H_G_A) as (_ & Par_E_H_A_G & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_E_H_A_G) as Par_A_G_E_H.
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_C_d_f_E Col_f_E_H neq_H_E) as Par_C_d_H_E.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_C_d_H_E) as Par_H_E_C_d.
	pose proof (lemma_parallelflip _ _ _ _ Par_H_E_C_d) as (_ & Par_H_E_d_C & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_K_d) as (_ & _ & Col_d_C_K & _ & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_H_E_d_C Col_d_C_K neq_K_C) as Par_H_E_K_C.
	pose proof (lemma_parallelflip _ _ _ _ Par_H_E_K_C) as (_ & _ & Par_E_H_C_K).
	pose proof (lemma_paralleldef2B _ _ _ _ Par_E_H_C_K) as TarskiPar_E_H_C_K.

	destruct TarskiPar_E_H_C_K as (_ & _ & _ & SS_C_K_E_H).

	pose proof (lemma_parallelNC _ _ _ _ Par_E_H_C_K) as (_ & _ & _ & nCol_E_H_K).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_G_H_K) as BetS_K_H_G.
	pose proof (lemma_s_os _ _ _ _ _ BetS_K_H_G Col_E_H_H nCol_E_H_K) as OS_K_E_H_G.
	pose proof (lemma_planeseparation _ _ _ _ _ SS_C_K_E_H OS_K_E_H_G) as OS_C_E_H_G.

	destruct OS_C_E_H_G as (Q & BetS_C_Q_G & Col_E_H_Q & nCol_E_H_C).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_C_d_E_f) as Par_E_f_C_d.
	pose proof (lemma_paralleldef2B _ _ _ _ Par_E_f_C_d) as TarskiPar_E_f_C_d.

	destruct TarskiPar_E_f_C_d as (_ & _ & _ & SS_C_d_E_f).

	pose proof (lemma_samesidesymmetric _ _ _ _ SS_C_d_E_f) as (SS_d_C_E_f & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_E_H_Q) as (Col_H_E_Q & _ & _ & _ & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_H_E_f Col_H_E_Q neq_H_E) as Col_E_f_Q.
	pose proof (lemma_parallelNC _ _ _ _ Par_C_d_E_f) as (_ & nCol_C_E_f & _ & _).
	pose proof (lemma_NCorder _ _ _ nCol_C_E_f) as (_ & nCol_E_f_C & _ & _ & _).
	pose proof (lemma_s_os _ _ _ _ _ BetS_C_Q_G Col_E_f_Q nCol_E_f_C) as OS_C_E_f_G.
	pose proof (lemma_planeseparation _ _ _ _ _ SS_d_C_E_f OS_C_E_f_G) as OS_d_E_f_G.

	destruct OS_d_E_f_G as (P & BetS_d_P_G & Col_E_f_P & nCol_E_f_d).

	(* assert (~ ~ Cross A f G H \/ Cross A E G H) as n_n_Cross_A_f_G_H | Cross_A_E_G_H. *)
	assert (~ ~ (Cross A f G H \/ Cross A E G H)) as n_n_Cross_A_f_G_H_or_Cross_A_E_G_H.
	{
		intro n_Cross_A_f_G_H_and_n_Cross_A_E_G_H.

		apply Classical_Prop.not_or_and in n_Cross_A_f_G_H_and_n_Cross_A_E_G_H.
		destruct n_Cross_A_f_G_H_and_n_Cross_A_E_G_H as (n_Cross_A_f_G_H & n_Cross_A_E_G_H).

		pose proof (lemma_30helper _ _ _ _ _ _ Par_A_b_E_f BetS_A_G_b BetS_E_H_f n_Cross_A_f_G_H) as Cross_A_E_G_H.

		contradict Cross_A_E_G_H.
		exact n_Cross_A_E_G_H.
	}
	assert (Cross_A_f_G_H_or_Cross_A_E_G_H := n_n_Cross_A_f_G_H_or_Cross_A_E_G_H).
	apply Classical_Prop.NNPP in Cross_A_f_G_H_or_Cross_A_E_G_H.


	assert (~ ~ (Cross C f K H \/ Cross C E K H)) as n_n_Cross_C_f_K_H_or_Cross_C_E_K_H.
	{
		intro n_Cross_C_f_K_H_and_n_Cross_C_E_K_H.

		apply Classical_Prop.not_or_and in n_Cross_C_f_K_H_and_n_Cross_C_E_K_H.
		destruct n_Cross_C_f_K_H_and_n_Cross_C_E_K_H as (n_Cross_C_f_K_H & n_Cross_C_E_K_H).

		pose proof (lemma_30helper _ _ _ _ _ _ Par_C_d_E_f BetS_C_K_d BetS_E_H_f n_Cross_C_f_K_H) as Cross_C_E_K_H.

		contradict Cross_C_E_K_H.
		exact n_Cross_C_E_K_H.
	}
	assert (Cross_C_f_K_H_or_Cross_C_E_K_H := n_n_Cross_C_f_K_H_or_Cross_C_E_K_H).
	apply Classical_Prop.NNPP in Cross_C_f_K_H_or_Cross_C_E_K_H.

	pose proof (lemma_collinearorder _ _ _ Col_E_F_H) as (Col_F_E_H & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_G) as (Col_B_A_G & _ & _ & _ & _).
	pose proof (lemma_parallelflip _ _ _ _ Par_A_B_E_F) as (_ & Par_A_B_F_E & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_A_B_F_E Col_F_E_H neq_H_E) as Par_A_B_H_E.
	pose proof (lemma_parallelflip _ _ _ _ Par_A_B_H_E) as (_ & Par_A_B_E_H & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_A_B_E_H) as Par_E_H_A_B.
	pose proof (lemma_parallelflip _ _ _ _ Par_E_H_A_B) as (_ & Par_E_H_B_A & _).
	pose proof (lemma_parallelNC _ _ _ _ Par_A_G_E_H) as (_ & _ & _ & nCol_A_G_H).
	pose proof (lemma_parallelflip _ _ _ _ Par_C_D_E_F) as (_ & Par_C_D_F_E & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_C_D_F_E Col_F_E_H neq_H_E) as Par_C_D_H_E.
	pose proof (lemma_parallelflip _ _ _ _ Par_C_D_H_E) as (_ & Par_C_D_E_H & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_C_D_E_H) as Par_E_H_C_D.
	pose proof (lemma_parallelflip _ _ _ _ Par_E_H_C_D) as (_ & Par_E_H_D_C & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_D_K) as (Col_D_C_K & _ & _ & _ & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_E_H_D_C Col_D_C_K neq_K_C) as Par_E_H_K_C.
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_E_H_C_K) as Par_C_K_E_H.
	pose proof (lemma_parallelNC _ _ _ _ Par_C_K_E_H) as (_ & _ & _ & nCol_C_K_H).
	pose proof (lemma_NCorder _ _ _ nCol_C_K_H) as (_ & nCol_K_H_C & _ & _ & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_H_f) as (neq_H_f & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_H_f) as neq_f_H.
	pose proof (lemma_NChelper _ _ _ _ _ nCol_E_H_K Col_E_H_f Col_E_H_H neq_f_H) as nCol_f_H_K.
	pose proof (lemma_NCorder _ _ _ nCol_f_H_K) as (_ & _ & _ & _ & nCol_K_H_f).
	pose proof (lemma_s_col_eq_B_C K H H eq_H_H) as Col_K_H_H.

	(* assert by cases *)
	assert (Par A b C d) as Par_A_b_C_d.
	destruct Cross_A_f_G_H_or_Cross_A_E_G_H as [Cross_A_f_G_H | Cross_A_E_G_H].
	{
		(* case Cross_A_f_G_H *)
		pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_A_f_G_H nCol_A_G_H) as (OS_A_G_H_f & _ & _ & _).

		(* assert by cases *)
		assert (Par A b C d) as Par_A_b_C_d.
		destruct Cross_C_f_K_H_or_Cross_C_E_K_H as [Cross_C_f_K_H | Cross_C_E_K_H].
		{
			(* case Cross_C_f_K_H *)
			pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_C_f_K_H nCol_C_K_H) as (_ & _ & _ & OS_f_H_K_C).
			pose proof (proposition_30A _ _ _ _ _ _ _ _ _ Par_A_b_E_f Par_C_d_E_f BetS_G_H_K BetS_A_G_b BetS_E_H_f BetS_C_K_d OS_A_G_H_f OS_f_H_K_C) as Par_A_b_C_d.

			exact Par_A_b_C_d.
		}
		{
			(* case Cross_C_E_K_H *)

			destruct Cross_C_E_K_H as (M & BetS_C_M_E & BetS_K_M_H).
			pose proof (lemma_s_col_BetS_A_B_C K M H BetS_K_M_H) as Col_K_M_H.
			pose proof (lemma_collinearorder _ _ _ Col_K_M_H) as (_ & _ & _ & Col_K_H_M & _).
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_H_f) as BetS_f_H_E.
			pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_K_H_H Col_K_H_M BetS_f_H_E BetS_C_M_E nCol_K_H_f nCol_K_H_C) as SS_f_C_K_H.
			assert (eq K K) as eq_K_K by (reflexivity).
			pose proof (lemma_s_col_eq_A_C K H K eq_K_K) as Col_K_H_K.
			pose proof (lemma_s_os _ _ _ _ _ BetS_C_K_d Col_K_H_K nCol_K_H_C) as OS_C_K_H_d.
			pose proof (lemma_planeseparation _ _ _ _ _ SS_f_C_K_H OS_C_K_H_d) as OS_f_K_H_d.

			destruct OS_f_K_H_d as (m & BetS_f_m_d & Col_K_H_m & _).
			pose proof (lemma_parallelsymmetric _ _ _ _ Par_C_d_f_E) as Par_f_E_C_d.

			pose proof (parnotmeet _ _ _ _ Par_f_E_C_d) as n_Meet_f_E_C_d.
			pose proof (lemma_collinearorder _ _ _ Col_E_f_H) as (_ & Col_f_H_E & _ & _ & _).
			pose proof (lemma_betweennotequal _ _ _ BetS_C_K_d) as (neq_K_d & _ & _).
			pose proof (lemma_collinearorder _ _ _ Col_K_H_m) as (Col_H_K_m & _ & _ & _ & _).
			pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_f_H_E Col_C_K_d neq_f_E neq_C_d neq_f_H neq_K_d n_Meet_f_E_C_d BetS_f_m_d Col_H_K_m) as BetS_H_m_K.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_m_K) as BetS_K_m_H.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_f_m_d) as BetS_d_m_f.

			assert (Cross d f K H) as Cross_d_f_K_H.
			unfold Cross.
			exists m.
			split.
			exact BetS_d_m_f.
			exact BetS_K_m_H.

			pose proof (lemma_inequalitysymmetric _ _ neq_K_d) as neq_d_K.
			pose proof (lemma_s_col_eq_B_C C K K eq_K_K) as Col_C_K_K.
			pose proof (lemma_NChelper _ _ _ _ _ nCol_C_K_H Col_C_K_d Col_C_K_K neq_d_K) as nCol_d_K_H.
			pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_d_f_K_H nCol_d_K_H) as (_ & OS_d_H_K_f & _ & _).
			pose proof (lemma_parallelflip _ _ _ _ Par_C_d_E_f) as (Par_d_C_E_f & _ & _).
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_K_d) as BetS_d_K_C.
			pose proof (lemma_oppositesidesymmetric _ _ _ _ OS_d_H_K_f) as OS_f_H_K_d.

			epose proof (proposition_30A A b d C _ f _ H K Par_A_b_E_f Par_d_C_E_f BetS_G_H_K BetS_A_G_b BetS_E_H_f BetS_d_K_C OS_A_G_H_f OS_f_H_K_d) as Par_A_b_d_C.
			pose proof (lemma_parallelflip _ _ _ _ Par_A_b_d_C) as (_ & Par_A_b_C_d & _).

			exact Par_A_b_C_d.
		}

		exact Par_A_b_C_d.
	}
	{
		(* case Cross_A_E_G_H *)

		(* assert by cases *)
		assert (Par A b C d) as Par_A_b_C_d.
		destruct Cross_C_f_K_H_or_Cross_C_E_K_H as [Cross_C_f_K_H | Cross_C_E_K_H].
		{
			(* case Cross_C_f_K_H *)

			destruct Cross_C_f_K_H as (M & BetS_C_M_f & BetS_K_M_H).
			pose proof (lemma_s_col_BetS_A_B_C K M H BetS_K_M_H) as Col_K_M_H.
			pose proof (lemma_collinearorder _ _ _ Col_K_M_H) as (_ & _ & _ & Col_K_H_M & _).
			pose proof (lemma_NCorder _ _ _ nCol_E_H_K) as (_ & _ & _ & _ & nCol_K_H_E).
			pose proof (lemma_s_ss _ _ _ _ _ _ _ Col_K_H_H Col_K_H_M BetS_E_H_f BetS_C_M_f nCol_K_H_E nCol_K_H_C) as SS_E_C_K_H.
			assert (eq K K) as eq_K_K by (reflexivity).
			pose proof (lemma_s_col_eq_A_C K H K eq_K_K) as Col_K_H_K.
			pose proof (lemma_s_os _ _ _ _ _ BetS_C_K_d Col_K_H_K nCol_K_H_C) as OS_C_K_H_d.
			pose proof (lemma_planeseparation _ _ _ _ _ SS_E_C_K_H OS_C_K_H_d) as OS_E_K_H_d.

			destruct OS_E_K_H_d as (m & BetS_E_m_d & Col_K_H_m & _).
			pose proof (parnotmeet _ _ _ _ Par_E_f_C_d) as n_Meet_E_f_C_d.
			pose proof (lemma_betweennotequal _ _ _ BetS_C_K_d) as (neq_K_d & _ & _).
			pose proof (lemma_collinearorder _ _ _ Col_K_H_m) as (Col_H_K_m & _ & _ & _ & _).
			pose proof (lemma_collinearbetween _ _ _ _ _ _ _ Col_E_H_f Col_C_K_d neq_E_f neq_C_d neq_E_H neq_K_d n_Meet_E_f_C_d BetS_E_m_d Col_H_K_m) as BetS_H_m_K.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_H_m_K) as BetS_K_m_H.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_m_d) as BetS_d_m_E.


			assert (Cross d E K H) as Cross_d_E_K_H.
			unfold Cross.
			exists m.
			split.
			exact BetS_d_m_E.
			exact BetS_K_m_H.

			pose proof (lemma_inequalitysymmetric _ _ neq_K_d) as neq_d_K.
			pose proof (lemma_s_col_eq_B_C C K K eq_K_K) as Col_C_K_K.
			pose proof (lemma_NChelper _ _ _ _ _ nCol_C_K_H Col_C_K_d Col_C_K_K neq_d_K) as nCol_d_K_H.
			pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_d_E_K_H nCol_d_K_H) as (_ & OS_d_H_K_E & _ & _).
			pose proof (lemma_parallelflip _ _ _ _ Par_C_d_f_E) as (Par_d_C_f_E & _ & _).
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_K_d) as BetS_d_K_C.
			pose proof (lemma_oppositesidesymmetric _ _ _ _ OS_d_H_K_E) as OS_E_H_K_d.
			pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_A_E_G_H nCol_A_G_H) as (OS_A_G_H_E & _ & _ & _).
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_H_f) as BetS_f_H_E.
			pose proof (proposition_30A _ _ _ _ _ _ _ _ _ Par_A_b_f_E Par_d_C_f_E BetS_G_H_K BetS_A_G_b BetS_f_H_E BetS_d_K_C OS_A_G_H_E OS_E_H_K_d) as Par_A_b_d_C.
			pose proof (lemma_parallelflip _ _ _ _ Par_A_b_d_C) as (_ & Par_A_b_C_d & _).

			exact Par_A_b_C_d.
		}
		{
			(* case Cross_C_E_K_H *)
			pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_C_E_K_H nCol_C_K_H) as (_ & OS_C_H_K_E & _ & _).
			pose proof (lemma_oppositesidesymmetric _ _ _ _ OS_C_H_K_E) as OS_E_H_K_C.
			pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_A_E_G_H nCol_A_G_H) as (OS_A_G_H_E & _ & _ & _).
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_H_f) as BetS_f_H_E.

			epose proof (proposition_30A A b C d f E G H K Par_A_b_f_E Par_C_d_f_E BetS_G_H_K BetS_A_G_b BetS_f_H_E BetS_C_K_d OS_A_G_H_E OS_E_H_K_C) as Par_A_b_C_d.

			exact Par_A_b_C_d.
		}

		exact Par_A_b_C_d.
	}
	pose proof (lemma_parallelflip _ _ _ _ Par_A_b_C_d) as (_ & Par_A_b_d_C & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_d_D) as (Col_d_C_D & _ & _ & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_C_D) as neq_D_C.
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_A_b_d_C Col_d_C_D neq_D_C) as Par_A_b_D_C.
	pose proof (lemma_parallelflip _ _ _ _ Par_A_b_D_C) as (_ & Par_A_b_C_D & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_A_b_C_D) as Par_C_D_A_b.
	pose proof (lemma_parallelflip _ _ _ _ Par_C_D_A_b) as (_ & Par_C_D_b_A & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_b_B) as (Col_b_A_B & _ & _ & _ & _).
	pose proof (lemma_parallelNC _ _ _ _ Par_A_B_E_F) as (nCol_A_B_E & _ & _ & _).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_E) as (_ & _ & _ & neq_B_A & _ & _).
	pose proof (lemma_collinearparallel _ _ _ _ _ Par_C_D_b_A Col_b_A_B neq_B_A) as Par_C_D_B_A.
	pose proof (lemma_parallelflip _ _ _ _ Par_C_D_B_A) as (_ & Par_C_D_A_B & _).
	pose proof (lemma_parallelsymmetric _ _ _ _ Par_C_D_A_B) as Par_A_B_C_D.

	exact Par_A_B_C_D.
Qed.

End Euclid.