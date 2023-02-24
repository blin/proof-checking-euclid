Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_collinear_ABC_ABD_ABE_CDE :
	forall A B C D E,
	neq A B ->
	Col A B C ->
	Col A B D ->
	Col A B E ->
	Col C D E.
Proof.
	intros A B C D E.
	intros neq_A_B.
	intros Col_A_B_C.
	intros Col_A_B_D.
	intros Col_A_B_E.

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_C Col_A_B_D neq_A_B) as Col_B_C_D.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_C Col_A_B_E neq_A_B) as Col_B_C_E.
	assert (eq B C \/ neq B C) as [eq_B_C|neq_B_C] by (apply Classical_Prop.classic).
	{
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_D Col_A_B_E neq_A_B) as Col_B_D_E.
		assert (Col_C_D_E := Col_B_D_E).
		replace B with C in Col_C_D_E.
		exact Col_C_D_E.
	}
	{
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_C_D Col_B_C_E neq_B_C) as Col_C_D_E.
		exact Col_C_D_E.
	}
Qed.

End Euclid.
