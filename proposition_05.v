Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.proposition_04.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_05 :
	forall A B C,
	isosceles A B C ->
	CongA A B C A C B.
Proof.
	intros A B C.
	intros isosceles_A_B_C.

	destruct isosceles_A_B_C as (Triangle_ABC & Cong_AB_AC).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AB_AC) as Cong_AC_AB.

	assert (nCol A B C) as nCol_A_B_C by (exact Triangle_ABC).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (_ & _ & nCol_C_A_B & _).
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_C_A_B) as CongA_CAB_BAC.

	pose proof (
		proposition_04
		_ _ _ _ _ _
		Cong_AC_AB
		Cong_AB_AC
		CongA_CAB_BAC
	) as (_ & _ & CongA_ABC_ACB).
	exact CongA_ABC_ACB.
Qed.

End Euclid.
