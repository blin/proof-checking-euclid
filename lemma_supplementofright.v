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
	intros Supp_A_B_C_D_F.
	intros RightTriangle_A_B_C.


	destruct Supp_A_B_C_D_F as (OnRay_B_C_D & BetS_A_B_F).
	pose proof (lemma_s_col_BetS_A_B_C A B F BetS_A_B_F) as Col_A_B_F.
	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_F) as (neq_B_F & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_B_F) as neq_F_B.
	pose proof (lemma_collinearright _ _ _ _ RightTriangle_A_B_C Col_A_B_F neq_F_B) as RightTriangle_F_B_C.
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_F_B_C OnRay_B_C_D) as RightTriangle_F_B_D.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_F_B_D) as RightTriangle_D_B_F.
	
	split.
	exact RightTriangle_F_B_D.
	exact RightTriangle_D_B_F.
Qed.

End Euclid.
