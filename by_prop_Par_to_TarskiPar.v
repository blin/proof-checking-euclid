Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_SameSide.
Require Import ProofCheckingEuclid.by_def_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_TarskiPar_collinear.
Require Import ProofCheckingEuclid.by_prop_TarskiPar_flip.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_Par_to_TarskiPar :
	forall A B C D,
	Par A B C D ->
	TarskiPar A B C D.
Proof.
	intros A B C D.
	intros Par_AB_CD.

	destruct Par_AB_CD as (a & b & c & d & e & neq_A_B & neq_C_D & Col_A_B_a & Col_A_B_b & neq_a_b & Col_C_D_c & Col_C_D_d & neq_c_d & n_Meet_A_B_C_D & BetS_a_e_d & BetS_c_e_b).

	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_neq_symmetric _ _ neq_C_D) as neq_D_C.
	pose proof (by_prop_neq_symmetric _ _ neq_a_b) as neq_b_a.

	pose proof (by_prop_Col_order _ _ _ Col_A_B_a) as (Col_B_A_a & Col_B_a_A & Col_a_A_B & Col_A_a_B & Col_a_B_A).
	pose proof (by_prop_Col_order _ _ _ Col_A_B_b) as (Col_B_A_b & Col_B_b_A & Col_b_A_B & Col_A_b_B & Col_b_B_A).
	pose proof (by_prop_Col_order _ _ _ Col_C_D_c) as (Col_D_C_c & Col_D_c_C & Col_c_C_D & Col_C_c_D & Col_c_D_C).
	pose proof (by_prop_Col_order _ _ _ Col_C_D_d) as (Col_D_C_d & Col_D_d_C & Col_d_C_D & Col_C_d_D & Col_d_D_C).


	pose proof (axiom_betweennesssymmetry _ _ _ BetS_a_e_d) as BetS_d_e_a.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_a_e_d) as (neq_e_d & neq_a_e & neq_a_d).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_d_e_a) as (neq_e_a & neq_d_e & neq_d_a).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_e_b) as BetS_b_e_c.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_c_e_b) as (neq_e_b & neq_c_e & neq_c_b).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_b_e_c) as (neq_e_c & neq_b_e & neq_b_c).

	assert (~ Meet a b C D) as n_Meet_a_b_C_D.
	{
		intro Meet_a_b_C_D.

		destruct Meet_a_b_C_D as (R & _ & _ & Col_a_b_R & Col_C_D_R).

		pose proof (by_prop_Col_order _ _ _ Col_a_b_R) as (Col_b_a_R & _ & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_B_a Col_A_B_b neq_A_B) as Col_B_a_b.
		pose proof (by_prop_Col_order _ _ _ Col_B_a_b) as (_ & _ & _ & _ & Col_b_a_B).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_b_a_B Col_b_a_R neq_b_a) as Col_a_B_R.

		(* assert by cases *)
		assert (Col A B R) as Col_A_B_R.
		assert (eq a B \/ neq a B) as [eq_a_B|neq_a_B] by (apply Classical_Prop.classic).
		{
			(* case eq_a_B *)
			assert (neq A a) as neq_A_a by (rewrite eq_a_B; exact neq_A_B).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_A_a Col_B_A_b neq_B_A) as Col_A_a_b.
			pose proof (by_prop_Col_order _ _ _ Col_A_a_b) as (_ & _ & _ & _ & Col_b_a_A).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_b_a_A Col_b_a_R neq_b_a) as Col_a_A_R.
			pose proof (by_prop_neq_symmetric _ _ neq_A_a) as neq_a_A.
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_a_A_R Col_a_A_B neq_a_A) as Col_A_R_B.
			pose proof (by_prop_Col_order _ _ _ Col_A_R_B) as (_ & _ & _ & Col_A_B_R & _).

			exact Col_A_B_R.
		}
		{
			(* case neq_a_B *)
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_a_B_R Col_a_B_A neq_a_B) as Col_B_R_A.
			pose proof (by_prop_Col_order _ _ _ Col_B_R_A) as (_ & _ & Col_A_B_R & _ & _).

			exact Col_A_B_R.
		}
		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_R Col_C_D_R) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	pose proof (lemma_extension _ _ _ _ neq_e_b neq_e_b) as (P & BetS_e_b_P & Cong_bP_eb).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_e_b_P) as BetS_P_b_e.
	pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_P_b_e BetS_b_e_c) as BetS_P_b_c.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_b_c) as BetS_c_b_P.

	assert (~ Col a d P) as n_Col_a_d_P.
	{
		intro Col_a_d_P.

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_a_e_d) as Col_a_e_d.
		pose proof (by_prop_Col_order _ _ _ Col_a_e_d) as (_ & _ & _ & Col_a_d_e & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_a_d_P Col_a_d_e neq_a_d) as Col_d_P_e.
		pose proof (by_prop_Col_order _ _ _ Col_d_P_e) as (_ & _ & _ & _ & Col_e_P_d).
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_e_b_P) as Col_e_b_P.
		pose proof (by_prop_Col_order _ _ _ Col_e_b_P) as (_ & _ & _ & Col_e_P_b & _).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_e_b_P) as (_ & _ & neq_e_P).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_e_P_d Col_e_P_b neq_e_P) as Col_P_d_b.
		pose proof (by_prop_Col_order _ _ _ Col_P_d_b) as (Col_d_P_b & _ & _ & _ & _).
		pose proof (by_prop_Col_order _ _ _ Col_a_d_P) as (_ & Col_d_P_a & _ & _ & _).

		assert (~ eq d P) as n_eq_d_P.
		{
			intro eq_d_P.

			pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_c_b_P) as Col_c_b_P.
			assert (Col c b d) as Col_c_b_d by (rewrite eq_d_P; exact Col_c_b_P).
			pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_b_e_c) as Col_b_e_c.
			pose proof (by_prop_Col_order _ _ _ Col_b_e_c) as (_ & _ & Col_c_b_e & _ & _).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_c_b_d Col_c_b_e neq_c_b) as Col_b_d_e.
			pose proof (by_prop_Col_order _ _ _ Col_a_d_e) as (_ & Col_d_e_a & _ & _ & _).
			pose proof (by_prop_Col_order _ _ _ Col_b_d_e) as (_ & Col_d_e_b & _ & _ & _).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_d_e_a Col_d_e_b neq_d_e) as Col_e_a_b.
			pose proof (by_prop_Col_order _ _ _ Col_a_e_d) as (Col_e_a_d & _ & _ & _ & _).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_e_a_b Col_e_a_d neq_e_a) as Col_a_b_d.
			pose proof (by_def_Meet _ _ _ _ _ neq_a_b neq_C_D Col_a_b_d Col_C_D_d) as Meet_a_b_C_D.

			contradict Meet_a_b_C_D.
			exact n_Meet_a_b_C_D.
		}
		assert (neq_d_P := n_eq_d_P).


		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_d_P_b Col_d_P_a neq_d_P) as Col_P_b_a.
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_P_b_c) as Col_P_b_c.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_e_b_P) as (neq_b_P & _ & _).
		pose proof (by_prop_neq_symmetric _ _ neq_b_P) as neq_P_b.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_P_b_a Col_P_b_c neq_P_b) as Col_b_a_c.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_B_a Col_A_B_b neq_A_B) as Col_B_a_b.
		pose proof (by_prop_Col_order _ _ _ Col_B_a_b) as (_ & _ & _ & _ & Col_b_a_B).
		pose proof (by_prop_Col_order _ _ _ Col_b_a_c) as (Col_a_b_c & _ & _ & _ & _).
		assert (eq c c) as eq_c_c by (reflexivity).
		pose proof (by_def_Meet _ _ _ _ _ neq_a_b neq_C_D Col_a_b_c Col_C_D_c) as Meet_a_b_C_D.

		contradict Meet_a_b_C_D.
		exact n_Meet_a_b_C_D.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_a_d_P) as nCol_a_d_P.

	pose proof (postulate_Pasch_outer _ _ _ _ _ BetS_P_b_e BetS_a_e_d nCol_a_d_P) as (M & BetS_P_M_d & BetS_a_b_M).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_a_b_M) as BetS_M_b_a.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_a_b_M) as Col_a_b_M.
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_B_a Col_A_B_b neq_A_B) as Col_B_a_b.
	pose proof (by_prop_Col_order _ _ _ Col_B_a_b) as (_ & _ & _ & _ & Col_b_a_B).
	pose proof (by_prop_Col_order _ _ _ Col_a_b_M) as (Col_b_a_M & _ & _ & _ & _).
	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_b_a_B Col_b_a_M neq_b_a) as Col_a_B_M.

	(* assert by cases *)
	assert (Col A B M) as Col_A_B_M.
	assert (eq a B \/ neq a B) as [eq_a_B|neq_a_B] by (apply Classical_Prop.classic).
	{
		(* case eq_a_B *)
		assert (neq A a) as neq_A_a by (rewrite eq_a_B; exact neq_A_B).
		assert (Col A a b) as Col_A_a_b by (rewrite eq_a_B; exact Col_A_B_b).
		pose proof (by_prop_Col_order _ _ _ Col_A_a_b) as (_ & _ & _ & _ & Col_b_a_A).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_b_a_A Col_b_a_M neq_b_a) as Col_a_A_M.
		pose proof (by_prop_neq_symmetric _ _ neq_A_a) as neq_a_A.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_a_A_M Col_a_A_B neq_a_A) as Col_A_M_B.
		pose proof (by_prop_Col_order _ _ _ Col_A_M_B) as (_ & _ & _ & Col_A_B_M & _).

		exact Col_A_B_M.
	}
	{
		(* case neq_a_B *)
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_a_B_M Col_a_B_A neq_a_B) as Col_B_M_A.
		pose proof (by_prop_Col_order _ _ _ Col_B_M_A) as (_ & _ & Col_A_B_M & _ & _).

		exact Col_A_B_M.
	}
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_M_d) as BetS_d_M_P.

	assert (~ Col A B c) as n_Col_A_B_c.
	{
		intro Col_A_B_c.

		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_c Col_C_D_c) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_B_c) as nCol_A_B_c.


	assert (~ Col A B d) as n_Col_A_B_d.
	{
		intro Col_A_B_d.

		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_d Col_C_D_d) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_A_B_d) as nCol_A_B_d.

	pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_A_B_b Col_A_B_M BetS_c_b_P BetS_d_M_P nCol_A_B_c nCol_A_B_d) as SameSide_c_d_AB.

	assert (~ Meet A B c d) as n_Meet_A_B_c_d.
	{
		intro Meet_A_B_c_d.

		destruct Meet_A_B_c_d as (R & _ & _ & Col_A_B_R & Col_c_d_R).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_C_D_c Col_C_D_d neq_C_D) as Col_D_c_d.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_C_c Col_D_C_d neq_D_C) as Col_C_c_d.
		pose proof (by_prop_Col_order _ _ _ Col_C_c_d) as (_ & Col_c_d_C & _ & _ & _).
		pose proof (by_prop_Col_order _ _ _ Col_D_c_d) as (_ & Col_c_d_D & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_c_d Col_c_d_C Col_c_d_D Col_c_d_R) as Col_C_D_R.
		pose proof (by_def_Meet _ _ _ _ _ neq_A_B neq_C_D Col_A_B_R Col_C_D_R) as Meet_A_B_C_D.

		contradict Meet_A_B_C_D.
		exact n_Meet_A_B_C_D.
	}

	pose proof (by_def_TarskiPar _ _ _ _ neq_A_B neq_c_d n_Meet_A_B_c_d SameSide_c_d_AB) as TarskiPar_AB_cd.

	assert (eq C C) as eq_C_C by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C C D C eq_C_C) as Col_C_D_C.
	pose proof (by_prop_Col_ABC_ABD_ABE_CDE _ _ _ _ _ neq_C_D Col_C_D_c Col_C_D_d Col_C_D_C) as Col_c_d_C.

	assert (~ ~ TarskiPar A B C D) as n_n_TarskiPar_AB_CD.
	{
		intro n_TarskiPar_AB_CD.

		assert (~ neq C d) as n_neq_C_d.
		{
			intro neq_C_d.

			pose proof (by_prop_TarskiPar_collinear _ _ _ _ _ TarskiPar_AB_cd Col_c_d_C neq_C_d) as TarskiPar_AB_Cd.
			pose proof (by_prop_TarskiPar_flip _ _ _ _ TarskiPar_AB_Cd) as (_ & TarskiPar_AB_dC & _).
			pose proof (by_prop_TarskiPar_collinear _ _ _ _ _ TarskiPar_AB_dC Col_d_C_D neq_D_C) as TarskiPar_AB_DC.
			pose proof (by_prop_TarskiPar_flip _ _ _ _ TarskiPar_AB_DC) as (_ & TarskiPar_AB_CD & _).

			contradict TarskiPar_AB_CD.
			exact n_TarskiPar_AB_CD.
		}
		assert (eq_C_d := n_neq_C_d).
		apply Classical_Prop.NNPP in eq_C_d.


		assert (TarskiPar A B c C) as TarskiPar_AB_cC by (rewrite eq_C_d; exact TarskiPar_AB_cd).
		pose proof (by_prop_TarskiPar_collinear _ _ _ _ _ TarskiPar_AB_cC Col_c_C_D neq_D_C) as TarskiPar_AB_DC.
		pose proof (by_prop_TarskiPar_flip _ _ _ _ TarskiPar_AB_DC) as (_ & TarskiPar_AB_CD & _).

		contradict TarskiPar_AB_CD.
		exact n_TarskiPar_AB_CD.
	}
	assert (TarskiPar_AB_CD := n_n_TarskiPar_AB_CD).
	apply Classical_Prop.NNPP in TarskiPar_AB_CD.

	exact TarskiPar_AB_CD.
Qed.

End Euclid.
