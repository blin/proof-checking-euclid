Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_isosceles.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_Lt_trichotomous.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_angletrichotomy.
Require Import ProofCheckingEuclid.proposition_05.
Require Import ProofCheckingEuclid.proposition_18.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_19 :
	forall A B C,
	Triangle A B C ->
	LtA B C A A B C ->
	Lt A B A C.
Proof.
	intros A B C.
	intros Triangle_ABC.
	intros LtA_BCA_ABC.

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_ABC) as nCol_A_B_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (_ & nCol_B_C_A & _ & nCol_A_C_B & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & _ & neq_A_C & _ & _ & _).

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_B_C) as CongA_ABC_CBA.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_C_A) as CongA_BCA_ACB.
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_A_B_C) as CongA_ABC_ABC.

	pose proof (by_def_Triangle _ _ _ nCol_A_C_B) as Triangle_ACB.

	assert (~ Cong A C A B) as n_Cong_AC_AB.
	{
		intro Cong_AC_AB.

		pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AC_AB) as Cong_AB_AC.
		pose proof (by_def_isosceles _ _ _ Triangle_ABC Cong_AB_AC) as isosceles_A_B_C.
		pose proof (proposition_05 _ _ _ isosceles_A_B_C) as CongA_ABC_ACB.
		pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ABC_ACB) as CongA_ACB_ABC.
		pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_BCA_ACB CongA_ACB_ABC) as CongA_BCA_ABC.
		pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_BCA_ABC CongA_BCA_ABC) as LtA_BCA_BCA.
		pose proof (lemma_angletrichotomy _ _ _ _ _ _ LtA_BCA_BCA) as n_LtA_BCA_BCA.

		contradict LtA_BCA_BCA.
		exact n_LtA_BCA_BCA.
	}

	assert (~ Lt A C A B) as n_Lt_AC_AB.
	{
		intro Lt_AC_AB.

		pose proof (proposition_18 _ _ _ Triangle_ACB Lt_AC_AB) as LtA_CBA_ACB.
		pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_CBA_ACB CongA_ABC_CBA) as LtA_ABC_ACB.
		pose proof (by_prop_LtA_respects_congruence _ _ _ _ _ _ _ _ _ LtA_ABC_ACB CongA_BCA_ACB) as LtA_ABC_BCA.
		pose proof (lemma_angletrichotomy _ _ _ _ _ _ LtA_ABC_BCA) as n_LtA_ABC_BCA.

		contradict LtA_BCA_ABC.
		exact n_LtA_ABC_BCA.
	}

	assert (~ ~ Lt A B A C) as Lt_AB_AC.
	{
		intro n_Lt_AB_AC.

		pose proof (by_prop_Lt_trichotomous _ _ _ _ n_Lt_AB_AC n_Lt_AC_AB neq_A_B neq_A_C) as Cong_AB_AC.
		pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AB_AC) as Cong_AC_AB.

		contradict Cong_AC_AB.
		exact n_Cong_AC_AB.
	}
	apply Classical_Prop.NNPP in Lt_AB_AC.

	exact Lt_AB_AC.
Qed.

End Euclid.
