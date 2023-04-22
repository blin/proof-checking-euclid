Require Import ProofCheckingEuclid.euclidean_axioms.

Section Definitions.

Context `{Ax:euclidean_neutral}.

(* C lies on ray AB *)
Definition OnRay A B C := exists X, BetS X A C /\ BetS X A B.
Definition Lt A B C D := exists X, BetS C X D /\ Cong C X A B.
Definition Midpoint A B C := BetS A B C /\ Cong A B B C.
Definition CongA A B C a b c := exists U V u v,
	OnRay B A U /\
	OnRay B C V /\
	OnRay b a u /\
	OnRay b c v /\
	Cong B U b u /\
	Cong B V b v /\
	Cong U V u v /\
	nCol A B C.
(* ∠ABC and ∠DBF are supplementary *)
Definition Supp A B C D F := OnRay B C D /\ BetS A B F.
Definition RightTriangle A B C := exists X,
	BetS A B X /\
	Cong A B X B /\
	Cong A C X C /\
	neq B C.
Definition Perp_at P Q A B C := exists X,
	Col P Q C /\
	Col A B C /\
	Col A B X /\
	RightTriangle X C P.
Definition InAngle A B C P := exists X Y, OnRay B A X /\ OnRay B C Y /\ BetS X P Y.
(* P and Q are on the same side of AB *)
(* TODO: rename to SameSide *)
Definition SS P Q A B := exists X U V,
	Col A B U /\
	Col A B V /\
	BetS P U X /\
	BetS Q V X /\
	nCol A B P /\
	nCol A B Q.
Definition isosceles A B C := Triangle A B C /\ Cong A B A C.
(* Cut is only used in proposition 10 and the original lemma_twolines *)
Definition Cut A B C D E := BetS A E B /\ BetS C E D /\ nCol A B C /\ nCol A B D.
Definition LtA A B C D E F := exists U X V, BetS U X V /\ OnRay E D U /\ OnRay E F V /\ CongA A B C D E X.
(* ABC and DEF make together two right angles *)
Definition SumTwoRT A B C D E F := exists X Y Z U V, Supp X Y U V Z /\ CongA A B C X Y U /\ CongA D E F V Y Z.
Definition SumA A B C D E F P Q R := exists X, CongA A B C P Q X /\ CongA D E F X Q R /\ BetS P X R.
Definition equilateral A B C := Cong A B B C /\ Cong B C C A.

End Definitions.
