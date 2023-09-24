Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_SameSide.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_planeseparation.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_samesidetransitive :
	forall A B P Q R,
	SameSide P Q A B ->
	SameSide Q R A B ->
	SameSide P R A B.
Proof.
	intros A B P Q R.
	intros SameSide_P_Q_A_B.
	intros SameSide_Q_R_A_B.


	destruct SameSide_Q_R_A_B as (G & E & F & Col_A_B_E & Col_A_B_F & BetS_Q_E_G & BetS_R_F_G & nCol_A_B_Q & nCol_A_B_R).
	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_Q_E_G Col_A_B_E nCol_A_B_Q) as OppositeSide_Q_A_B_G.
	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_P_Q_A_B OppositeSide_Q_A_B_G) as OppositeSide_P_A_B_G.

	destruct OppositeSide_P_A_B_G as (M & BetS_P_M_G & Col_A_B_M & nCol_A_B_P).
	pose proof (by_def_SameSide _ _ _ _ _ _ _ Col_A_B_M Col_A_B_F BetS_P_M_G BetS_R_F_G nCol_A_B_P nCol_A_B_R) as SameSide_P_R_A_B.

	exact SameSide_P_R_A_B.
Qed.

End Euclid.

