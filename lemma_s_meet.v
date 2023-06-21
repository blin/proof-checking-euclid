Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_meet :
	forall A B C D X,
	neq A B ->
	neq C D ->
	Col A B X ->
	Col C D X ->
	Meet A B C D.
Proof.
	intros A B C D X.
	intros neq_A_B.
	intros neq_C_D.
	intros Col_A_B_X.
	intros Col_C_D_X.

	unfold Meet.
	exists X.
	split.
	exact neq_A_B.
	split.
	exact neq_C_D.
	split.
	exact Col_A_B_X.
	exact Col_C_D_X.
Qed.

End Euclid.

