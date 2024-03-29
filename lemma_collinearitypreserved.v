Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_betweennesspreserved.


Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_collinearitypreserved :
	forall A B C a b c,
	Col A B C ->
	Cong A B a b ->
	Cong A C a c ->
	Cong B C b c ->
	Col a b c.
Proof.
	intros A B C a b c.
	intros Col_A_B_C.
	intros Cong_AB_ab.
	intros Cong_AC_ac.
	intros Cong_BC_bc.

	destruct Col_A_B_C as [eq_A_B | [eq_A_C | [eq_B_C | [BetS_B_A_C | [BetS_A_B_C | BetS_A_C_B]]]]].
	{
		(* case eq_A_B *)
		assert (Cong A A a b) as Cong_AA_ab by (setoid_rewrite eq_A_B at 2; exact Cong_AB_ab).
		pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AA_ab) as Cong_ab_AA.
		assert (~ neq a b) as eq_a_b.
		{
			intros neq_a_b.

			pose proof (axiom_nocollapse _ _ _ _ neq_a_b Cong_ab_AA) as neq_A_A.
			assert (eq A A) as eq_A_A by (reflexivity).

			contradict eq_A_A.
			exact neq_A_A.
		}
		apply Classical_Prop.NNPP in eq_a_b.
		pose proof (by_def_Col_from_eq_A_B a b c eq_a_b) as Col_a_b_c.
		exact Col_a_b_c.
	}
	{
		(* case eq_A_C *)
		assert (Cong A A a c) as Cong_AA_ac by (setoid_rewrite eq_A_C at 2; exact Cong_AC_ac).
		pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AA_ac) as Cong_ac_AA.
		assert (~ neq a c) as eq_a_c.
		{
			intros neq_a_c.

			pose proof (axiom_nocollapse _ _ _ _ neq_a_c Cong_ac_AA) as neq_A_A.
			assert (eq A A) as eq_A_A by (reflexivity).

			contradict eq_A_A.
			exact neq_A_A.
		}
		apply Classical_Prop.NNPP in eq_a_c.
		pose proof (by_def_Col_from_eq_A_C a b c eq_a_c) as Col_a_b_c.
		exact Col_a_b_c.
	}
	{
		(* case eq_B_C *)
		assert (Cong B B b c) as Cong_BB_bc by (setoid_rewrite eq_B_C at 2; exact Cong_BC_bc).
		pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BB_bc) as Cong_bc_BB.
		assert (~ neq b c) as eq_b_c.
		{
			intros neq_b_c.

			pose proof (axiom_nocollapse _ _ _ _ neq_b_c Cong_bc_BB) as neq_B_B.
			assert (eq B B) as eq_B_B by (reflexivity).

			contradict eq_B_B.
			exact neq_B_B.
		}
		apply Classical_Prop.NNPP in eq_b_c.
		pose proof (by_def_Col_from_eq_B_C a b c eq_b_c) as Col_a_b_c.
		exact Col_a_b_c.
	}
	{
		(* case BetS_B_A_C *)
		pose proof (cn_congruencereverse a b) as Cong_ab_ba.
		pose proof (cn_congruencereverse A B) as Cong_AB_BA.
		pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AB_ab Cong_ab_ba) as Cong_AB_ba.
		pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AB_BA) as Cong_BA_AB.
		pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_BA_AB Cong_AB_ba) as Cong_BA_ba.
		pose proof (
			lemma_betweennesspreserved _ _ _ _ _ _ Cong_BA_ba Cong_BC_bc Cong_AC_ac BetS_B_A_C
		) as BetS_b_a_c.
		pose proof (by_def_Col_from_BetS_B_A_C _ _ _ BetS_b_a_c) as Col_a_b_c.
		exact Col_a_b_c.
	}
	{
		(* case BetS_A_B_C *)
		pose proof (
			lemma_betweennesspreserved _ _ _ _ _ _ Cong_AB_ab Cong_AC_ac Cong_BC_bc BetS_A_B_C
		) as BetS_a_b_c.
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_a_b_c) as Col_a_b_c.
		exact Col_a_b_c.
	}
	{
		(* case BetS_A_C_B *)
		pose proof (cn_congruencereverse C B) as Cong_CB_BC.
		pose proof (cn_congruencereverse b c) as Cong_bc_cb.
		pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_CB_BC Cong_BC_bc) as Cong_CB_bc.
		pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_CB_bc Cong_bc_cb) as Cong_CB_cb.
		pose proof (
			lemma_betweennesspreserved _ _ _ _ _ _ Cong_AC_ac Cong_AB_ab Cong_CB_cb BetS_A_C_B
		) as BetS_a_c_b.
		pose proof (by_def_Col_from_BetS_A_C_B _ _ _ BetS_a_c_b) as Col_a_b_c.
		exact Col_a_b_c.
	}
Qed.

End Euclid.
