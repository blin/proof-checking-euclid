Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_def_CongTriangles :
	forall A B C a b c,
	Cong A B a b ->
	Cong B C b c ->
	Cong A C a c ->
	CongTriangles A B C a b c.
Proof.
	intros A B C a b c.
	intros Cong_AB_ab.
	intros Cong_BC_bc.
	intros Cong_AC_ac.

	unfold CongTriangles.
	split.
	exact Cong_AB_ab.
	split.
	exact Cong_BC_bc.
	exact Cong_AC_ac.
Qed.

End Euclid.
