Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_extensionunique :
	forall A B E F,
	BetS A B E -> BetS A B F -> Cong B E B F ->
	eq E F.
Proof.
	intros A B E F.
	intros BetS_A_B_E.
	intros BetS_A_B_F.
	intros Cong_BE_BF.
	assert (Cong A B A B) as Cong_AB_AB by (apply cn_congruencereflexive).
	assert (Cong A E A E) as Cong_AE_AE by (apply cn_congruencereflexive).
	assert (Cong B E B E) as Cong_BE_BE by (apply cn_congruencereflexive).
	assert (Cong E B E B) as Cong_EB_EB by (apply cn_congruencereflexive).
	apply by_prop_Cong_symmetric in Cong_BE_BF as Cong_BF_BE.

	(* BetS A B E -> Col A B E -> DegenerateTriangle A B E *)
	(* BetS A B E -> Col A B E -> DegenerateTriangle A B E *)
	(* eq E E -> Col E B E -> DegenerateTriangle E B E *)
	(* eq E F -> Col E B F -> DegenerateTriangle E B F *)
	(* axiom_5_line is used to help prove eq E F *)

	(* △ABE and △ABE are SSS congruent. *)
	(* △EBE and △EBF are SAS congruent. *)
	(* ∠ABE is supplement to ∠EBE and ∠ABE is supplement to ∠EBF . *)
	(* △EBE ≅ △EBF implies that EE ≅ FE . *)
	pose proof (
		axiom_5_line
		A B E E
		A B F E

		Cong_BE_BF
		Cong_AE_AE
		Cong_BE_BE
		BetS_A_B_E
		BetS_A_B_F
		Cong_AB_AB
	) as Cong_EE_EF.

	apply by_prop_Cong_symmetric in Cong_EE_EF as Cong_EF_EE.

	assert (~ neq E F) as eq_E_F.
	{
		intro neq_E_F.

		pose proof (axiom_nocollapse _ _ _ _ neq_E_F Cong_EF_EE) as neq_E_E.
		assert (eq E E) as eq_E_E by (reflexivity).

		contradict eq_E_E.
		exact neq_E_E.
	}
	unfold neq in eq_E_F.
	apply Classical_Prop.NNPP in eq_E_F.
	exact eq_E_F.
Qed.

End Euclid.


