Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_Lt_notequal :
	forall A B C D,
	Lt A B C D ->
	neq A B /\ neq C D.
Proof.
	intros A B C D.
	intros Lt_AB_CD.

	destruct Lt_AB_CD as (E & BetS_C_E_D & Cong_CE_AB).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_E_D) as (_ & neq_C_E & _).
	pose proof (axiom_nocollapse _ _ _ _ neq_C_E Cong_CE_AB) as neq_A_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_E_D) as (_ & _ & neq_C_D).

	split.
	exact neq_A_B.
	exact neq_C_D.
Qed.

End Euclid.
