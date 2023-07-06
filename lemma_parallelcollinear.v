Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.
Require Import ProofCheckingEuclid.lemma_tarski_parallel_collinear_ABcd_Ccd_ABCd.
Require Import ProofCheckingEuclid.lemma_tarski_parallel_collinear_ABcd_cCd_ABCd.
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
Require Import ProofCheckingEuclid.lemma_s_triangle.
Require Import ProofCheckingEuclid.lemma_tarskiparallelflip.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_parallelcollinear :
	forall A B C c d,
	TarskiPar A B c d ->
	Col c d C ->
	neq C d ->
	TarskiPar A B C d.
Proof.
	intros A B C c d.
	intros TarskiPar_A_B_c_d.
	intros Col_c_d_C.
	intros neq_C_d.


	assert (TarskiPar_A_B_c_d_2 := TarskiPar_A_B_c_d).
	destruct TarskiPar_A_B_c_d_2 as (neq_A_B & neq_c_d & n_Meet_A_B_c_d & SS_c_d_A_B).

	(* assert by cases *)
	assert (TarskiPar A B C d) as TarskiPar_A_B_C_d.
	destruct Col_c_d_C as [eq_c_d | [eq_c_C | [eq_d_C | [BetS_d_c_C | [BetS_c_d_C | BetS_c_C_d]]]]].
	{
		(* case eq_c_d *)

		contradict eq_c_d.
		exact neq_c_d.
	}
	{
		(* case eq_c_C *)
		assert (TarskiPar A B C d) as TarskiPar_A_B_C_d by (rewrite <- eq_c_C; exact TarskiPar_A_B_c_d).

		exact TarskiPar_A_B_C_d.
	}
	{
		(* case eq_d_C *)

		assert (~ ~ TarskiPar A B C d) as n_n_TarskiPar_A_B_C_d.
		{
			intro n_TarskiPar_A_B_C_d.
			pose proof (lemma_equalitysymmetric _ _ eq_d_C) as eq_C_d.
			contradict eq_C_d.
			exact neq_C_d.
		}
		assert (TarskiPar_A_B_C_d := n_n_TarskiPar_A_B_C_d).
		apply Classical_Prop.NNPP in TarskiPar_A_B_C_d.

		exact TarskiPar_A_B_C_d.
	}
	{
		(* case BetS_d_c_C *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_d_c_C) as BetS_C_c_d.
		pose proof (lemma_tarski_parallel_collinear_ABcd_Ccd_ABCd _ _ _ _ _ TarskiPar_A_B_c_d BetS_C_c_d) as TarskiPar_A_B_C_d.

		exact TarskiPar_A_B_C_d.
	}
	{
		(* case BetS_c_d_C *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_d_C) as BetS_C_d_c.
		pose proof (lemma_tarskiparallelflip _ _ _ _ TarskiPar_A_B_c_d) as (_ & TarskiPar_A_B_d_c & _).
		pose proof (lemma_tarski_parallel_collinear_ABcd_Ccd_ABCd _ _ _ _ _ TarskiPar_A_B_d_c BetS_C_d_c) as TarskiPar_A_B_C_c.
		pose proof (lemma_tarskiparallelflip _ _ _ _ TarskiPar_A_B_C_c) as (_ & TarskiPar_A_B_c_C & _).
		pose proof (lemma_tarski_parallel_collinear_ABcd_cCd_ABCd _ _ _ _ _ TarskiPar_A_B_c_C BetS_c_d_C) as TarskiPar_A_B_d_C.
		pose proof (lemma_tarskiparallelflip _ _ _ _ TarskiPar_A_B_d_C) as (_ & TarskiPar_A_B_C_d & _).

		exact TarskiPar_A_B_C_d.
	}
	{
		(* case BetS_c_C_d *)
		pose proof (lemma_tarski_parallel_collinear_ABcd_cCd_ABCd _ _ _ _ _ TarskiPar_A_B_c_d BetS_c_C_d) as TarskiPar_A_B_C_d.

		exact TarskiPar_A_B_C_d.
	}

	exact TarskiPar_A_B_C_d.
Qed.

End Euclid.
