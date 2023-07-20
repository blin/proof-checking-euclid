Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_collinear.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_leg_change.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_RightTriangle_supplement :
	forall A B C D F,
	Supp A B C D F ->
	RightTriangle A B C ->
	RightTriangle F B D /\ RightTriangle D B F.
Proof.
	intros A B C D F.
	intros Supp_ABC_DBF.
	intros RightTriangle_ABC.


	destruct Supp_ABC_DBF as (OnRay_BC_D & BetS_A_B_F).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_B_F) as (neq_B_F & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_B_F) as neq_F_B.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_B_F) as Col_A_B_F.

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_ABC Col_A_B_F neq_F_B) as RightTriangle_FBC.
	pose proof (by_prop_RightTriangle_leg_change _ _ _ _ RightTriangle_FBC OnRay_BC_D) as RightTriangle_FBD.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_FBD) as RightTriangle_DBF.

	split.
	exact RightTriangle_FBD.
	exact RightTriangle_DBF.
Qed.

End Euclid.
