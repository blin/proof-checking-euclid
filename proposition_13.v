Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NChelper.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.by_def_SumTwoRT.
Require Import ProofCheckingEuclid.by_def_Supp.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_13 :
	forall A B C D,
	BetS D B C ->
	nCol A B C ->
	SumTwoRT C B A A B D.
Proof.
	intros A B C D.
	intros BetS_D_B_C.
	intros nCol_A_B_C.

	pose proof (lemma_betweennotequal _ _ _ BetS_D_B_C) as (_ & neq_D_B & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_B_C) as BetS_C_B_D.
	assert (Col C B D) as Col_C_B_D by (unfold Col; one_of_disjunct BetS_C_B_D).

	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (_ & _ & _ & neq_B_A & _ & _).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (_ & _ & _ & _ & nCol_C_B_A).

	pose proof (lemma_s_onray_assert_ABB _ _ neq_B_A) as OnRay_BA_A.

	assert (eq B B) as eq_B_B by (reflexivity).
	assert (Col C B B) as Col_C_B_B by (unfold Col; one_of_disjunct eq_B_B).

	pose proof (lemma_NChelper _ _ _ _ _ nCol_C_B_A Col_C_B_D Col_C_B_B neq_D_B) as nCol_D_B_A.
	pose proof (lemma_NCorder _ _ _ nCol_D_B_A) as (_ & _ & _ & _ & nCol_A_B_D).

	pose proof (lemma_equalanglesreflexive _ _ _ nCol_A_B_D) as CongA_ABD_ABD.
	pose proof (lemma_equalanglesreflexive _ _ _ nCol_C_B_A) as CongA_CBA_CBA.

	pose proof (by_def_Supp _ _ _ _ _ OnRay_BA_A BetS_C_B_D) as Supp_CBA_ABD.

	pose proof (by_def_SumTwoRT _ _ _ _ _ _ _ _ _ _ _ Supp_CBA_ABD CongA_CBA_CBA CongA_ABD_ABD) as SumTwoRT_CBA_ABD.

	exact SumTwoRT_CBA_ABD.
Qed.

End Euclid.
