(** The following axiom systems are used to formalize
    Euclid's proofs of Euclid's Elements.OriginalProofs.statements. *)

(** First, we define an axiom system for neutral geometry,
    i.e. geometry without continuity axioms nor parallel postulate.
 *)

Class euclidean_neutral :=
{
  Point : Type;
  Circle : Type;
  Cong : Point -> Point -> Point -> Point -> Prop;
  BetS : Point -> Point -> Point -> Prop;
  CI : Circle -> Point -> Point -> Point -> Prop;
  eq := @eq Point;
  neq A B := ~ eq A B;
  Col A B C := (eq A B \/ eq A C \/ eq B C \/ BetS B A C \/ BetS A B C \/ BetS A C B);

  OnCirc B J := exists X Y U, CI J U X Y /\ Cong U B X Y;
  InCirc P J := exists X Y U V W, CI J U V W /\ (eq P U \/ (BetS U Y X /\ Cong U X V W /\ Cong U P U Y));
  OutCirc P J := exists X U V W, CI J U V W /\ BetS U X P /\ Cong U X V W;

  axiom_circle_center_radius :
   forall A B C J P, CI J A B C -> OnCirc P J -> Cong A P B C;
  postulate_Euclid3 : forall A B, neq A B -> exists X, CI X A A B;
}.

(** Second, we enrich the axiom system with line-circle
     and circle-circle continuity axioms.
    Those two axioms state that we allow ruler and compass
    constructions.
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
