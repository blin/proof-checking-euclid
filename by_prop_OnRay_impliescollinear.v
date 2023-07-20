Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_OnRay_impliescollinear :
	forall A B C,
	OnRay A B C ->
	Col A B C.
Proof.
	intros A B C.
	intros OnRay_AB_C.

	unfold OnRay in OnRay_AB_C.

	destruct OnRay_AB_C as (J & BetS_J_A_C & BetS_J_A_B).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_J_A_C) as (_ & neq_J_A & _).

	assert (Col J A B) as Col_J_A_B.
	unfold Col.
	one_of_disjunct BetS_J_A_B.

	assert (Col J A C) as Col_J_A_C.
	unfold Col.
	one_of_disjunct BetS_J_A_C.

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_J_A_B Col_J_A_C neq_J_A) as Col_A_B_C.
	exact Col_A_B_C.
Qed.

End Euclid.
