Require Import ProofCheckingEuclid.euclidean_axioms.

Section Definitions.

Context `{Ax:euclidean_neutral}.

Definition equilateral A B C := Cong A B B C /\ Cong B C C A.

End Definitions.
