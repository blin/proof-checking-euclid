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
(* C and D are on opposite sides of AB *)
Definition OppositeSide P A B Q := exists X, BetS P X Q /\ Col A B X /\ nCol A B P.
(* P and Q are on the same side of AB *)
Definition SameSide P Q A B := exists X U V,
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
(* AB and CD are together greater than EF *)
Definition TogetherGreater A B C D E F := exists X, BetS A B X /\ Cong B X C D /\ Lt E F A X.
(* AB and CD are together greater than EF and GH *)
(* TT is only used in proposition 21 *)
Definition TT A B C D E F G H := exists X, BetS E F X /\ Cong F X G H /\ TogetherGreater A B C D E X.
(* ABC and DEF make together two right angles *)
Definition SumTwoRT A B C D E F := exists X Y Z U V, Supp X Y U V Z /\ CongA A B C X Y U /\ CongA D E F V Y Z.
Definition Meet A B C D := exists X,
	neq A B /\
	neq C D /\
	Col A B X /\
	Col C D X.
Definition Cross A B C D := exists X, BetS A X B /\ BetS C X D.
Definition TarskiPar A B C D := neq A B /\ neq C D /\ ~ Meet A B C D /\ SameSide C D A B.
(* BetS U X v /\ BetS u X V is used as "same plane". See "Tarski-parallel" in the paper. *)
Definition Par A B C D := exists U V u v X,
	neq A B /\
	neq C D /\
	Col A B U /\
	Col A B V /\
	neq U V /\
	Col C D u /\
	Col C D v /\
	neq u v /\
	~ Meet A B C D /\
	BetS U X v /\
	BetS u X V.
Definition AngleSum A B C D E F P Q R := exists X, CongA A B C P Q X /\ CongA D E F X Q R /\ BetS P X R.
Definition Parallelogram A B C D := Par A B C D /\ Par A D B C.
Definition Square A B C D :=
	Cong A B C D /\
	Cong A B B C /\
	Cong A B D A /\
	RightTriangle D A B /\
	RightTriangle A B C /\
	RightTriangle B C D /\
	RightTriangle C D A.
Definition equilateral A B C := Cong A B B C /\ Cong B C C A.

End Definitions.
