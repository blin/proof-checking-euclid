Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_collinearorder.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_oppositesideflip :
	forall A B P Q,
	OppositeSide P A B Q ->
	OppositeSide P B A Q.
Proof.
	intros A B P Q.
	intros OppositeSide_P_AB_Q.

	destruct OppositeSide_P_AB_Q as (r & BetS_P_r_Q & Col_A_B_r & nCol_A_B_P).

	pose proof (lemma_NCorder _ _ _ nCol_A_B_P) as (nCol_B_A_P & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_r) as (Col_B_A_r & _ & _ & _ & _).

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_P_r_Q Col_B_A_r nCol_B_A_P) as OppositeSide_P_BA_Q.

	exact OppositeSide_P_BA_Q.
Qed.

End Euclid.
