Require Import ProofCheckingEuclid.by_def_InCirc_center.
Require Import ProofCheckingEuclid.euclidean_axioms.


Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_localextension :
	forall A B Q,
	neq A B ->
	neq B Q ->
	exists X,
	BetS A B X /\ Cong B X B Q.
Proof.
	intros A B Q.
	intros neq_A_B.
	intros neq_B_Q.

	pose proof (
		postulate_Euclid3
		B Q
		neq_B_Q
	) as (J & CI_J_B_BQ).

	pose proof (by_def_InCirc_center _ _ _ _ CI_J_B_BQ) as InCirc_B_J.

	pose proof (
		postulate_line_circle
		A B B J B Q
		CI_J_B_BQ
		InCirc_B_J
		neq_A_B
	) as (
		X & Y &
		Col_A_B_X &
		BetS_A_B_Y &
		OnCirc_X_J &
		OnCirc_Y_J &
		BetS_X_B_Y
	).

	exists Y.
	split.
	exact BetS_A_B_Y.

	pose proof (
		axiom_circle_center_radius
		B B Q J Y
		CI_J_B_BQ
		OnCirc_Y_J
	) as Cong_BY_BQ.
	exact Cong_BY_BQ.

Qed.

End Euclid.
