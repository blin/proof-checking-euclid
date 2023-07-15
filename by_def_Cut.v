Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_Cut :
	forall A B C D E,
	BetS A E B ->
	BetS C E D ->
	nCol A B C ->
	nCol A B D ->
	Cut A B C D E.
Proof.
	intros A B C D E.
	intros BetS_A_E_B.
	intros BetS_C_E_D.
	intros nCol_A_B_C.
	intros nCol_A_B_D.

	unfold Cut.
	split.
	exact BetS_A_E_B.
	split.
	exact BetS_C_E_D.
	split.
	exact nCol_A_B_C.
	exact nCol_A_B_D.
Qed.

End Euclid.
