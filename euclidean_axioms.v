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
	(* ABC and abc are congruent triangles *)
	CongTriangles A B C a b c := Cong A B a b /\ Cong B C b c /\ Cong A C a c;
	(* P and Q are on opposite sides of AB *)
	OppositeSide P A B Q := exists X, BetS P X Q /\ Col A B X /\ nCol A B P;
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


	(*
		In inner Pasch asserted point is between (inside)
		a point on the extension of one side and a point on another side.
		In outer Pasch asserted point is following (outside)
		a point on the extension of one side and a point on another side.
	*)
	postulate_Pasch_inner :
		forall C D A E B,
			BetS C E A -> BetS D B A -> nCol C A D ->
			exists X, BetS C X B /\ BetS D X E;
	postulate_Pasch_outer :
		forall C D B E A,
			BetS C E B -> BetS D B A -> nCol D A C ->
			exists X, BetS C X A /\ BetS D E X;

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

(** Last, we enrich the axiom system with axioms for equality of areas. *)

Class area `(Ax : euclidean_euclidean) :=
{
	EqAreaQuad : Point -> Point -> Point -> Point -> Point -> Point -> Point -> Point -> Prop;
	EqAreaTri : Point -> Point -> Point -> Point -> Point -> Point -> Prop;
	axiom_congruentequal :
		forall A B C a b c, CongTriangles A B C a b c -> EqAreaTri A B C a b c;
	axiom_EqAreaTri_permutation :
		forall A B C a b c,
			EqAreaTri A B C a b c ->
			EqAreaTri A B C b c a /\
			EqAreaTri A B C a c b /\
			EqAreaTri A B C b a c /\
			EqAreaTri A B C c b a /\
			EqAreaTri A B C c a b;
	axiom_EqAreaTri_symmetric :
		forall A B C a b c,
			EqAreaTri A B C a b c ->
			EqAreaTri a b c A B C;
	axiom_EqAreaQuad_permutation :
		forall A B C D a b c d,
			EqAreaQuad A B C D a b c d ->
			EqAreaQuad A B C D b c d a /\
			EqAreaQuad A B C D d c b a /\
			EqAreaQuad A B C D c d a b /\
			EqAreaQuad A B C D b a d c /\
			EqAreaQuad A B C D d a b c /\
			EqAreaQuad A B C D c b a d /\
			EqAreaQuad A B C D a d c b;
	axiom_halvesofequals :
		forall A B C D a b c d,
			EqAreaTri A B C B C D ->
			OppositeSide A B C D ->
			EqAreaTri a b c b c d ->
			OppositeSide a b c d ->
			EqAreaQuad A B D C a b d c ->
			EqAreaTri A B C a b c;

	axiom_EqAreaQuad_symmetric :
		forall A B C D a b c d,
			EqAreaQuad A B C D a b c d ->
			EqAreaQuad a b c d A B C D;
	axiom_EqAreaQuad_transitive :
		forall A B C D P Q R S a b c d,
			EqAreaQuad A B C D a b c d ->
			EqAreaQuad a b c d P Q R S ->
			EqAreaQuad A B C D P Q R S;
	axiom_EqAreaTri_transitive :
		forall A B C P Q R a b c,
			EqAreaTri A B C a b c ->
			EqAreaTri a b c P Q R ->
			EqAreaTri A B C P Q R;

	cn_differenceofparts_Tri_Tri_sharedvertex :
		forall A B C D E a b c d e,
			BetS A B C ->
			BetS a b c ->
			BetS E D C ->
			BetS e d c ->
			EqAreaTri B C D b c d ->
			EqAreaTri A C E a c e ->
			EqAreaQuad A B D E a b d e;
	axiom_cutoff2 :
		forall A B C D E a b c d e,
			BetS B C D ->
			BetS b c d ->
			EqAreaTri C D E c d e ->
			EqAreaQuad A B D E a b d e ->
			EqAreaQuad A B C E a b c e;
	axiom_deZolt1 :
		forall B C D E, BetS B E D -> ~ EqAreaTri D B C E B C;
	axiom_deZolt2 :
		forall A B C E F, Triangle A B C -> BetS B E A -> BetS B F C -> ~ EqAreaTri A B C E B F;
	cn_sumofparts_Quad_Tri_sharedside :
		forall A B C D E M a b c d e m,
			BetS B C D ->
			BetS b c d ->
			EqAreaTri C D E c d e ->
			EqAreaQuad A B C E a b c e ->
			BetS A M D ->
			BetS B M E ->
			BetS a m d ->
			BetS b m e ->
			EqAreaQuad A B D E a b d e;
	cn_sumofparts_Tri_Tri_sharedside :
		forall A B C D M a b c d m,
			EqAreaTri A B C a b c ->
			EqAreaTri A B D a b d ->
			BetS C M D ->
			(BetS A M B \/ eq A M \/ eq M B) ->
			BetS c m d ->
			(BetS a m b \/ eq a m \/ eq m b) ->
			EqAreaQuad A C B D a c b d;
	axiom_paste4 :
		forall A B C D F G H J K L M P e m,
			EqAreaQuad A B m D F K H G->
			EqAreaQuad D B e C G H M L ->
			BetS A P C->
			BetS B P D->
			BetS K H M->
			BetS F G L ->
			BetS B m D->
			BetS B e C->
			BetS F J M->
			BetS K J L ->
			EqAreaQuad A B C D F K M L;

}.
