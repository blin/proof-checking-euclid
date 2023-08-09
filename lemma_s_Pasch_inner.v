Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_Pasch_inner :
	forall A B C D E,
	BetS A B D ->
	BetS A E C ->
	nCol A C D ->
	exists X, BetS D X E /\ BetS B X C.
Proof.
	intros A B C D E.
	intros BetS_A_B_D.
	intros BetS_A_E_C.
	intros nCol_A_C_D.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_D) as BetS_D_B_A.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_C) as BetS_C_E_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_C_D) as (nCol_C_A_D & nCol_C_D_A & nCol_D_A_C & nCol_A_D_C & nCol_D_C_A).
	pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_C_E_A BetS_D_B_A nCol_C_A_D) as (X & BetS_C_X_B & BetS_D_X_E).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_X_B) as BetS_B_X_C.

	exists X.
	split.
	exact BetS_D_X_E.
	exact BetS_B_X_C.
Qed.

End Euclid.
