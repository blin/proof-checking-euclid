Require Coq.Setoids.Setoid.
(*
	The following axiom systems are used to formalize
	Euclid's proofs of Euclid's Elements.OriginalProofs.statements.
*)

(*
	First, we define an axiom system for neutral geometry,
	i.e. geometry without continuity axioms nor parallel postulate.
*)

Class euclidean_neutral :=
{
	Point : Type;
	Circle : Type;
	Cong : Point -> Point -> Point -> Point -> Prop;
	BetS : Point -> Point -> Point -> Prop;
	(* TODO: rename to Circle *)
	CI : Circle -> Point -> Point -> Point -> Prop;
	eq := @eq Point;
	neq A B := ~ eq A B;
	nCol A B C := neq A B /\ neq A C /\ neq B C /\ ~ BetS A B C /\ ~ BetS A C B /\ ~ BetS B A C;
	Col A B C := (eq A B \/ eq A C \/ eq B C \/ BetS B A C \/ BetS A B C \/ BetS A C B);
	Triangle A B C := nCol A B C;


	OnCirc B J := exists X Y U, CI J U X Y /\ Cong U B X Y;
	InCirc P J := exists X Y U V W, CI J U V W /\ (eq P U \/ (BetS U Y X /\ Cong U X V W /\ Cong U P U Y));
	OutCirc P J := exists X U V W, CI J U V W /\ BetS U X P /\ Cong U X V W;

	cn_congruencetransitive :
		forall A B C D E F, Cong A B C D -> Cong A B E F -> Cong C D E F;
	cn_congruencereflexive :
		forall A B, Cong A B A B;
	(* Originally known as cn_equalityreverse *)
	cn_congruencereverse :
		forall A B, Cong A B B A;
	cn_sumofparts :
		forall A B C a b c,
			Cong A B a b -> Cong B C b c -> BetS A B C -> BetS a b c -> Cong A C a c;


	axiom_circle_center_radius :
		forall A B C J P, CI J A B C -> OnCirc P J -> Cong A P B C;
	axiom_betweennessidentity :
		forall A B, ~ BetS A B A;
	axiom_betweennesssymmetry :
		forall A B C, BetS A B C -> BetS C B A;
	(* Originally known as axiom_innertransitivity *)
	axiom_orderofpoints_ABD_BCD_ABC :
		forall A B C D,
			BetS A B D -> BetS B C D -> BetS A B C;
	axiom_connectivity :
		forall A B C D,
			BetS A B D -> BetS A C D -> ~ BetS A B C -> ~ BetS A C B ->
			eq B C;



	axiom_nocollapse :
		forall A B C D, neq A B -> Cong A B C D -> neq C D;
	(* 6.4 Five-line axiom *)
	(* Called Five Segment in Tarski *)
	axiom_5_line :
		forall A B C D a b c d,
			Cong B C b c ->
			Cong A D a d ->
			Cong B D b d ->
			BetS A B C ->
			BetS a b c ->
			Cong A B a b ->
			Cong D C d c;
	(*
		Below is a version of the five-line axiom that
		I've used up until having to prove lemma_Euclid4.
		The order and list of antecedents is changed to make the axiom easier to remember.

		0.	Not stated: ∃ △ABD , △abd , △DBC , △dbc , possibly degenerate.

		1.	△ABD ≅ △abd by SSS congruence.

		2.	(B(A,B,C) /\ B(a,b,c)) implies that
			∠ABD is supplement to ∠DBC and ∠abd is supplement to ∠dbc .
		3.	#1 implies that ∠ABD ≅ ∠abd .
		4.	#2 and #3 imply that ∠DBC ≅ ∠dbc .

		5.	(DB ≅ db /\ ∠DBC ≅ ∠dbc (from #4) /\ BC ≅ bc) implies that
			△DBC ≅ △dbc by SAS congruence.
	*)
	(*
		Adding lemma_5_line_degenerate would make it obvious when degenerate triangles are used.
		This is not done, since axiom_5_line is commonly used to help prove betweenness or equality,
		which are needed to show that the triangles used are in fact degenerate.
	*)
	(*
	axiom_5_line :
		forall A B C D a b c d,
			Cong A B a b ->
			Cong B D b d ->
			Cong D A d a ->

			BetS A B C ->
			BetS a b c ->

			Cong D B d b ->
			Cong B C b c ->

			Cong C D c d;
	*)


	postulate_Pasch_inner :
		forall A B C P Q,
			BetS A P C -> BetS B Q C -> nCol A C B ->
			exists X, BetS A X Q /\ BetS B X P;
	postulate_Pasch_outer :
		forall A B C P Q,
			BetS A P C -> BetS B C Q -> nCol B Q A ->
			exists X, BetS A X Q /\ BetS B P X;

	postulate_Euclid2 : forall A B, neq A B -> exists X, BetS A B X;
	postulate_Euclid3 : forall A B, neq A B -> exists X, CI X A A B;
}.

(*
	Second, we enrich the axiom system with line-circle
	and circle-circle continuity axioms.
	Those two axioms state that we allow ruler and compass constructions.
*)

Class euclidean_neutral_ruler_compass `(Ax : euclidean_neutral) :=
{
	postulate_line_circle :
		forall A B C K P Q,
			CI K C P Q -> InCirc B K -> neq A B ->
			exists X Y, Col A B X /\ BetS A B Y /\ OnCirc X K /\ OnCirc Y K /\ BetS X B Y;
	postulate_circle_circle :
		forall C D F G J K P Q R S,
			CI J C R S -> InCirc P J ->
			OutCirc Q J -> CI K D F G ->
			OnCirc P K -> OnCirc Q K ->
			exists X, OnCirc X J /\ OnCirc X K
}.

(*
	Third, we introduce the famous fifth postulate of Euclid,
	which ensures that the geometry is
	Euclidean (i.e. not hyperbolic).
*)

Class euclidean_euclidean `(Ax : euclidean_neutral_ruler_compass) :=
{
	postulate_Euclid5 :
		forall a p q r s t,
			BetS r t s -> BetS p t q -> BetS r a q ->
			Cong p t q t -> Cong t r t s -> nCol p q s ->
			exists X, BetS p a X /\ BetS s q X
}.
