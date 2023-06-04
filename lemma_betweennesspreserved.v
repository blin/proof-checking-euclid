Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_localextension.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_betweennesspreserved :
	forall A B C a b c,
	Cong A B a b ->
	Cong A C a c ->
	Cong B C b c ->
	BetS A B C ->
	BetS a b c.
Proof.
	intros A B C a b c.
	intros Cong_AB_ab.
	intros Cong_AC_ac.
	intros Cong_BC_bc.
	intros BetS_A_B_C.

	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_C) as (neq_B_C & neq_A_B & neq_A_C).
	pose proof (axiom_nocollapse _ _ _ _ neq_A_B Cong_AB_ab) as neq_a_b.
	pose proof (axiom_nocollapse _ _ _ _ neq_B_C Cong_BC_bc) as neq_b_c.
	pose proof (lemma_localextension _ _ _ neq_a_b neq_b_c) as (d & BetS_a_b_d & Cong_bd_bc).

	pose proof (lemma_congruenceflip _ _ _ _ Cong_AC_ac) as (Cong_CA_ca & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_BC_bc) as (Cong_CB_cb & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_bd_bc) as Cong_bc_bd.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_BC_bc Cong_bc_bd) as Cong_BC_bd.

	(* BetS A B C -> Col A B C -> DegenerateTriangle A B C *)
	(* BetS a b c -> Col a b c -> DegenerateTriangle a b c *)
	(* eq C C -> Col C B C -> DegenerateTriangle C B C *)
	(* eq c d -> Col c b d -> DegenerateTriangle c b d *)
	(* axiom_5_line is used to help prove BetS a b c *)
	(* axiom_5_line is used to help prove eq c d *)

	(* △ABC and △abc are SSS congruent. *)
	(* △CBC and △cbd are SAS congruent. *)
	(* ∠ABC is supplement to ∠CBC and ∠abc is supplement to ∠cbd . *)
	(* △CBC ≅ △cbd implies that CC ≅ dc . *)
	pose proof (
		axiom_5_line
		A B C C
		a b d c

		Cong_BC_bd
		Cong_AC_ac
		Cong_BC_bc
		BetS_A_B_C
		BetS_a_b_d
		Cong_AB_ab
	) as Cong_CC_cd.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_CC_cd) as (Cong_CC_dc & _).
	pose proof (lemma_doublereverse _ _ _ _ Cong_CC_dc) as (Cong_cd_CC & _).

	assert (~ neq c d) as eq_c_d.
	{
		intro neq_c_d.
		pose proof (axiom_nocollapse _ _ _ _ neq_c_d Cong_cd_CC) as neq_C_C.
		unfold neq in neq_C_C.
		contradict neq_C_C.
		reflexivity.
	}
	unfold neq in eq_c_d.
	apply Classical_Prop.NNPP in eq_c_d.

	assert (BetS a b c) as BetS_a_b_c by (rewrite eq_c_d; exact BetS_a_b_d).
	exact BetS_a_b_c.
Qed.

End Euclid.
