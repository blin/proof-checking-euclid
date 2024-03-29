Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_prop_Cong_doublereverse.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_localextension.


Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_differenceofparts_eq_B_A :
	forall A B C a b c,
	Cong A B a b -> Cong A C a c -> BetS A B C -> BetS a b c -> eq B A ->
	Cong B C b c.
Proof.
	intros A B C a b c.
	intros Cong_AB_ab Cong_AC_ac.
	intros BetS_A_B_C BetS_a_b_c.
	intros eq_B_A.

	assert (Cong A A a b) as Cong_AA_ab by (setoid_rewrite <- eq_B_A at 2; exact Cong_AB_ab).
	apply by_prop_Cong_symmetric in Cong_AA_ab as Cong_ab_AA.

	assert (~ neq a b) as eq_a_b.
	{
		intro neq_a_b.

		pose proof (axiom_nocollapse _ _ _ _ neq_a_b Cong_ab_AA) as neq_A_A.
		assert (eq A A) as eq_A_A by (reflexivity).

		contradict eq_A_A.
		exact neq_A_A.
	}
	unfold neq in eq_a_b.
	apply Classical_Prop.NNPP in eq_a_b.

	pose proof(cn_congruencereflexive A C) as Cong_AC_AC.
	assert (Cong B C A C) as Cong_BC_AC by (rewrite eq_B_A; exact Cong_AC_AC).

	pose proof(cn_congruencereflexive a c) as Cong_ac_ac.
	assert (Cong b c a c) as Cong_bc_ac by (rewrite <- eq_a_b; exact Cong_ac_ac).

	apply by_prop_Cong_symmetric in Cong_bc_ac as Cong_ac_bc.

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AC_ac Cong_ac_bc) as Cong_AC_bc.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_BC_AC Cong_AC_bc) as Cong_BC_bc.

	exact Cong_BC_bc.
Qed.

Lemma lemma_differenceofparts_neq_B_A :
	forall A B C a b c,
	Cong A B a b -> Cong A C a c -> BetS A B C -> BetS a b c -> neq B A ->
	Cong B C b c.
Proof.
	intros A B C a b c.
	intros Cong_AB_ab.
	intros Cong_AC_ac.
	intros BetS_A_B_C.
	intros BetS_a_b_c.
	intros neq_B_A.

	assert (~ eq C A) as neq_C_A.
	{
		intros eq_C_A.

		assert (BetS A B A) as BetS_A_B_A by (setoid_rewrite <- eq_C_A at 2; exact BetS_A_B_C).
		pose proof (axiom_betweennessidentity A B) as nBetS_A_B_A.

		contradict BetS_A_B_A.
		exact nBetS_A_B_A.
	}

	apply by_prop_neq_symmetric in neq_C_A as neq_A_C.

	pose proof (lemma_localextension _ _ _ neq_C_A neq_A_C) as (E & BetS_C_A_E & Cong_AE_AC).

	pose proof (axiom_nocollapse _ _ _ _ neq_A_C Cong_AC_ac) as neq_a_c.
	apply by_prop_neq_symmetric in neq_a_c as neq_c_a.
	pose proof (lemma_localextension _ _ _ neq_c_a neq_a_c) as (e & BetS_c_a_e & Cong_ae_ac).

	apply by_prop_Cong_symmetric in Cong_ae_ac as Cong_ac_ae.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AC_ac Cong_ac_ae) as Cong_AC_ae.
	apply by_prop_Cong_symmetric in Cong_AC_ae as Cong_ae_AC.
	apply by_prop_Cong_symmetric in Cong_AE_AC as Cong_AC_AE.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_ae_AC Cong_AC_AE) as Cong_ae_AE.
	apply by_prop_Cong_doublereverse in Cong_ae_AE as (Cong_EA_ea & Cong_ea_EA).


	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_A_E) as BetS_E_A_C.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_a_e) as BetS_e_a_c.

	pose proof (
		cn_sumofparts E A C e a c Cong_EA_ea Cong_AC_ac BetS_E_A_C BetS_e_a_c
	) as Cong_EC_ec.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_EC_ec) as (Cong_CE_ce & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AC_ac) as (Cong_CA_ca & _).

	pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_E_A_C BetS_A_B_C) as BetS_E_A_B.
	pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_e_a_c BetS_a_b_c) as BetS_e_a_b.

	(* BetS E A C -> Col E A C -> DegenerateTriangle E A C *)
	(* BetS e a c -> Col e a c -> DegenerateTriangle e a c *)
	(* BetS A B C -> Col C A B -> DegenerateTriangle C A B *)
	(* BetS a b c -> Col c a b -> DegenerateTriangle c a b *)
	(* axiom_5_line is not needed to prove degeneracy of involved triangles. Rare case. *)

	(* △EAC and △eac are SSS congruent. *)
	(* △CAB and △cab are SAS congruent. *)
	(* ∠EAC is supplement to ∠CAB and ∠eac is supplement to ∠cab . *)
	(* △CAB ≅ △cab implies that BC ≅ bc . *)
	pose proof (
		axiom_5_line
		E A B C
		e a b c

		Cong_AB_ab
		Cong_EC_ec
		Cong_AC_ac
		BetS_E_A_B
		BetS_e_a_b
		Cong_EA_ea
	) as Cong_CB_cb.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_CB_cb) as (Cong_BC_bc & _ & _).

	exact Cong_BC_bc.
Qed.

Lemma lemma_differenceofparts :
	forall A B C a b c,
	Cong A B a b -> Cong A C a c -> BetS A B C -> BetS a b c ->
	Cong B C b c.
Proof.
	intros A B C a b c.
	intros Cong_AB_ab Cong_AC_ac.
	intros BetS_A_B_C BetS_a_b_c.

	assert (eq B A \/ neq B A) as eq_B_A_or_neq_B_A by (apply Classical_Prop.classic).

	destruct eq_B_A_or_neq_B_A as [eq_B_A | neq_B_A].
	{
		pose proof (
			lemma_differenceofparts_eq_B_A
			A B C a b c
			Cong_AB_ab Cong_AC_ac
			BetS_A_B_C BetS_a_b_c
			eq_B_A
		) as Cong_BC_bc.
		exact Cong_BC_bc.
	}
	{
		pose proof (
			lemma_differenceofparts_neq_B_A
			A B C a b c
			Cong_AB_ab Cong_AC_ac
			BetS_A_B_C BetS_a_b_c
			neq_B_A
		) as Cong_BC_bc.
		exact Cong_BC_bc.
	}
Qed.

End Euclid.
