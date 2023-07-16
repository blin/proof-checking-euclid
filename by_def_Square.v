Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_Square :
	forall A B C D,
	Cong A B C D ->
	Cong A B B C ->
	Cong A B D A ->
	RightTriangle D A B ->
	RightTriangle A B C ->
	RightTriangle B C D ->
	RightTriangle C D A ->
	Square A B C D.
Proof.
	intros A B C D.
	intros Cong_AB_CD.
	intros Cong_AB_BC.
	intros Cong_AB_DA.
	intros RightTriangle_DAB.
	intros RightTriangle_ABC.
	intros RightTriangle_BCD.
	intros RightTriangle_CDA.

	unfold Square.
	split.
	exact Cong_AB_CD.
	split.
	exact Cong_AB_BC.
	split.
	exact Cong_AB_DA.
	split.
	exact RightTriangle_DAB.
	split.
	exact RightTriangle_ABC.
	split.
	exact RightTriangle_BCD.
	exact RightTriangle_CDA.
Qed.

End Euclid.
