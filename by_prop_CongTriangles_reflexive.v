Require Import ProofCheckingEuclid.by_def_CongTriangles.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_CongTriangles_reflexive :
	forall A B C,
	Triangle A B C ->
	CongTriangles A B C A B C.
Proof.
	intros A B C.
	intros Triangle_ABC.

	pose proof (cn_congruencereflexive A B) as Cong_AB_AB.
	pose proof (cn_congruencereflexive B C) as Cong_BC_BC.
	pose proof (cn_congruencereflexive A C) as Cong_AC_AC.
	pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_AB_AB Cong_BC_BC Cong_AC_AC) as CongTriangles_ABC_ABC.

	exact CongTriangles_ABC_ABC.
Qed.

End Euclid.

