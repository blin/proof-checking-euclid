Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_localextension.
Require Import ProofCheckingEuclid.proposition_02.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_extension_eq_B_P :
	forall A B P Q,
	neq A B ->
	neq P Q ->
	eq B P ->
	exists X, BetS A B X /\ Cong B X P Q.
Proof.
	intros A B P Q.
	intros neq_A_B.
	intros neq_P_Q.
	intros eq_B_P.

	assert (neq B Q) as neq_B_Q by (rewrite eq_B_P; exact neq_P_Q).

	pose proof (lemma_localextension _ _ _ neq_A_B neq_B_Q) as (X & BetS_A_B_X & Cong_BX_BQ).

	assert (Cong B X P Q) as Cong_BX_PQ by (rewrite <- eq_B_P; exact Cong_BX_BQ).

	exists X.
	split.
	exact BetS_A_B_X.
	exact Cong_BX_PQ.
Qed.

Lemma lemma_extension_neq_B_P :
	forall A B P Q,
	neq A B ->
	neq P Q ->
	neq B P ->
	exists X, BetS A B X /\ Cong B X P Q.
Proof.
	intros A B P Q.
	intros neq_A_B.
	intros neq_P_Q.
	intros neq_B_P.

	pose proof (proposition_02 _ _ _ neq_B_P neq_P_Q) as (D & Cong_BD_PQ).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BD_PQ) as Cong_PQ_BD.
	pose proof (axiom_nocollapse _ _ _ _ neq_P_Q Cong_PQ_BD) as neq_B_D.

	pose proof (lemma_localextension _ _ _ neq_A_B neq_B_D) as (X & BetS_A_B_X & Cong_BX_BD).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_BX_BD Cong_BD_PQ) as Cong_BX_PQ.

	exists X.
	split.
	exact BetS_A_B_X.
	exact Cong_BX_PQ.
Qed.

Lemma lemma_extension :
	forall A B P Q,
	neq A B ->
	neq P Q ->
	exists X, BetS A B X /\ Cong B X P Q.
Proof.
	intros A B P Q.
	intros neq_A_B.
	intros neq_P_Q.

	assert (eq B P \/ neq B P) as eq_B_P_or_neq_B_P by (apply Classical_Prop.classic).
	destruct eq_B_P_or_neq_B_P as [eq_B_P | neq_B_P].
	{
		pose proof (
			lemma_extension_eq_B_P _ _ _ _ neq_A_B neq_P_Q eq_B_P
		) as (X & BetS_A_B_X & Cong_BX_PQ).

		exists X.
		split.
		exact BetS_A_B_X.
		exact Cong_BX_PQ.
	}
	{
		pose proof (
			lemma_extension_neq_B_P _ _ _ _ neq_A_B neq_P_Q neq_B_P
		) as (X & BetS_A_B_X & Cong_BX_PQ).

		exists X.
		split.
		exact BetS_A_B_X.
		exact Cong_BX_PQ.
	}
Qed.

End Euclid.
