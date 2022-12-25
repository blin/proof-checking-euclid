Require Import Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.

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
	apply lemma_congruencesymmetric in Cong_BE_BF as Cong_BF_BE.
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
	apply lemma_congruencesymmetric in Cong_EE_EF as Cong_EF_EE.

	assert (~ neq E F) as eq_E_F.
	{
		intro neq_E_F.
		pose proof (axiom_nocollapse E F E E neq_E_F Cong_EF_EE) as neq_E_E.
		assert (eq E E) as eq_E_E by (reflexivity).
		contradiction.
	}
	unfold neq in eq_E_F.
	apply NNPP in eq_E_F.
	exact eq_E_F.
Qed.

End Euclid.


