Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearright.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_right_triangle_leg_change.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_supplementofright :
	forall A B C D F,
	Supp A B C D F ->
	RightTriangle A B C ->
	RightTriangle F B D /\ RightTriangle D B F.
Proof.
	intros A B C D F.
	intros Supp_ABC_DBF.
	intros RightTriangle_ABC.


	destruct Supp_ABC_DBF as (OnRay_BC_D & BetS_A_B_F).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_F) as (neq_B_F & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_B_F) as neq_F_B.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_B_F) as Col_A_B_F.

	pose proof (lemma_collinearright _ _ _ _ RightTriangle_ABC Col_A_B_F neq_F_B) as RightTriangle_FBC.
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_FBC OnRay_BC_D) as RightTriangle_FBD.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_FBD) as RightTriangle_DBF.

	split.
	exact RightTriangle_FBD.
	exact RightTriangle_DBF.
Qed.

End Euclid.
