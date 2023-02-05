Require Import ProofCheckingEuclid.euclidean_axioms.

Section Definitions.

Context `{Ax:euclidean_neutral}.

(* C lies on ray AB *)
Definition OnRay A B C := exists X, BetS X A C /\ BetS X A B.
Definition Lt A B C D := exists X, BetS C X D /\ Cong C X A B.
Definition CongA A B C a b c := exists U V u v,
	 OnRay B A U /\
	 OnRay B C V /\
	 OnRay b a u /\
	 OnRay b c v /\
	 Cong B U b u /\
	 Cong B V b v /\
	 Cong U V u v /\
	 nCol A B C.
Definition isosceles A B C := Triangle A B C /\ Cong A B A C.
Definition Cut A B C D E := BetS A E B /\ BetS C E D /\ nCol A B C /\ nCol A B D.
Definition equilateral A B C := Cong A B B C /\ Cong B C C A.

End Definitions.
