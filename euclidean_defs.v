Require Import ProofCheckingEuclid.euclidean_axioms.

Section Definitions.

Context `{Ax:euclidean_neutral}.

Definition Lt A B C D := exists X, BetS C X D /\ Cong C X A B.
Definition equilateral A B C := Cong A B B C /\ Cong B C C A.

End Definitions.
