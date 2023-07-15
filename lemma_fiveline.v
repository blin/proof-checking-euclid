Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennesspreserved.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_interior5.
Require Import ProofCheckingEuclid.lemma_s_congruence_null_segment.
Require Coq.Logic.Classical_Prop.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_fiveline :
	forall A B C D a b c d,
	Col A B C ->
	Cong A B a b ->
	Cong B C b c ->
	Cong A D a d ->
	Cong C D c d ->
	Cong A C a c ->
	neq A C ->
	Cong B D b d.
Proof.
	intros A B C D a b c d.
	intros Col_A_B_C.
	intros Cong_AB_ab.
	intros Cong_BC_bc.
	intros Cong_AD_ad.
	intros Cong_CD_cd.
	intros Cong_AC_ac.
	intros neq_A_C.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_AC_ac) as (Cong_CA_ca & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AD_ad) as (Cong_DA_da & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_BC_bc) as (Cong_CB_cb & _ & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_CD_cd) as (Cong_DC_dc & _ & _).

	destruct Col_A_B_C as [eq_A_B | [eq_A_C | [eq_B_C | [BetS_B_A_C | [BetS_A_B_C | BetS_A_C_B]]]]].
	{
		(* case eq_A_B *)

		assert (Cong B B a b) as Cong_BB_ab by (setoid_rewrite <- eq_A_B at 1; exact Cong_AB_ab).
		assert (Cong B D a d) as Cong_BD_ad by (rewrite <- eq_A_B; exact Cong_AD_ad).
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BB_ab) as Cong_ab_BB.
		pose proof (lemma_s_congruence_null_segment _ _ _ Cong_ab_BB) as eq_a_b.
		assert (Cong B D b d) as Cong_BD_bd by (rewrite <- eq_a_b; exact Cong_BD_ad).

		exact Cong_BD_bd.
	}
	{
		(* case eq_A_C *)
		contradict eq_A_C.
		exact neq_A_C.
	}
	{
		(* case eq_B_C *)
		assert (Cong B B b c) as Cong_BB_bc by (setoid_rewrite eq_B_C at 2; exact Cong_BC_bc).
		assert (Cong B D c d) as Cong_BD_cd by (rewrite eq_B_C; exact Cong_CD_cd).
		pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BB_bc) as Cong_bc_BB.
		pose proof (lemma_s_congruence_null_segment _ _ _ Cong_bc_BB) as eq_b_c.
		assert (Cong B D b d) as Cong_BD_bd by (rewrite eq_b_c; exact Cong_BD_cd).

		exact Cong_BD_bd.
	}
	{
		(* case BetS_B_A_C *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_C) as BetS_C_A_B.
		pose proof (lemma_betweennesspreserved _ _ _ _ _ _ Cong_CA_ca Cong_CB_cb Cong_AB_ab BetS_C_A_B) as BetS_c_a_b.

		pose proof (
			axiom_5_line
			C A B D
			c a b d
			Cong_AB_ab
			Cong_CD_cd
			Cong_AD_ad
			BetS_C_A_B
			BetS_c_a_b
			Cong_CA_ca
		) as Cong_DB_db.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_DB_db) as (Cong_BD_bd & _ & _).
		exact Cong_BD_bd.
	}
	{
		(* case BetS_A_B_C *)
		pose proof (lemma_betweennesspreserved _ _ _ _ _ _ Cong_AB_ab Cong_AC_ac Cong_BC_bc BetS_A_B_C) as BetS_a_b_c.
		pose proof (
			lemma_interior5
			_ _ _ _
			_ _ _ _
			BetS_A_B_C
			BetS_a_b_c
			Cong_AB_ab
			Cong_BC_bc
			Cong_AD_ad
			Cong_CD_cd
		) as Cong_BD_bd.
		exact Cong_BD_bd.
	}
	{
		(* case BetS_A_C_B *)
		pose proof (lemma_betweennesspreserved _ _ _ _ _ _ Cong_AC_ac Cong_AB_ab Cong_CB_cb BetS_A_C_B) as BetS_a_c_b.
		pose proof (
			axiom_5_line
			A C B D
			a c b d
			Cong_CB_cb
			Cong_AD_ad
			Cong_CD_cd
			BetS_A_C_B
			BetS_a_c_b
			Cong_AC_ac
		) as Cong_DB_db.
		pose proof (lemma_congruenceflip _ _ _ _ Cong_DB_db) as (Cong_BD_bd & _ & _).
		exact Cong_BD_bd.
	}
Qed.

End Euclid.
