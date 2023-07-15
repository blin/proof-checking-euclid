Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Coq.Logic.Classical_Prop.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

(* TODO: apply where appropriate, like in lemma_extensionunique *)
Lemma lemma_s_congruence_null_segment :
	forall A B C,
	Cong A B C C ->
	eq A B.
Proof.
	intros A B C.
	intros Cong_AB_CC.

	assert (eq C C) as eq_C_C by (reflexivity).

	assert (~ neq A B) as eq_A_B.
	{
		intros neq_A_B.

		pose proof (axiom_nocollapse _ _ _ _ neq_A_B Cong_AB_CC) as neq_C_C.

		contradict eq_C_C.
		exact neq_C_C.
	}
	apply Classical_Prop.NNPP in eq_A_B.

	exact eq_A_B.
Qed.

End Euclid.
