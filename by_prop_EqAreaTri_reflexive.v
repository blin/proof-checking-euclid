Require Import ProofCheckingEuclid.by_prop_CongTriangles_reflexive.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:area}.

Lemma by_prop_EqAreaTri_reflexive :
	forall A B C,
	Triangle A B C ->
	EqAreaTri A B C A B C.
Proof.
	intros A B C.
	intros Triangle_ABC.

	pose proof (by_prop_CongTriangles_reflexive _ _ _ Triangle_ABC) as CongTriangles_ABC_ABC.
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_ABC_ABC) as EqAreaTri_A_B_C_A_B_C.

	exact EqAreaTri_A_B_C_A_B_C.
Qed.

End Euclid.

