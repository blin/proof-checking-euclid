Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Meet.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E .
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_Par.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_def_Square.
Require Import ProofCheckingEuclid.by_def_TarskiPar.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col .
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol .
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_OnRay_assert.
Require Import ProofCheckingEuclid.by_prop_OnRay_impliescollinear.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_CBA_n_ACB.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_collinear.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_equaltoright.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_leg_change.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_SameSide_flip.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Playfair.
Require Import ProofCheckingEuclid.lemma_altitudeofrighttriangle.
Require Import ProofCheckingEuclid.lemma_betweennesspreserved.
Require Import ProofCheckingEuclid.lemma_erectedperpendicularunique.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_sameside_onray_EFAC_BFG_EGAC.
Require Import ProofCheckingEuclid.lemma_squareparallelogram.
Require Import ProofCheckingEuclid.lemma_twoperpsparallel.
Require Import ProofCheckingEuclid.proposition_12.
Require Import ProofCheckingEuclid.proposition_29C.
Require Import ProofCheckingEuclid.proposition_34.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_47A :
	forall A B C D E,
	Triangle A B C ->
	RightTriangle B A C ->
	Square B C E D ->
	OppositeSide D C B A ->
	exists X Y, Parallelogram B X Y D /\ BetS B X C /\ Parallelogram X C E Y /\ BetS D Y E /\ BetS Y X A /\ RightTriangle D Y A.
Proof.
	intros A B C D E.
	intros Triangle_A_B_C.
	intros RightTriangle_B_A_C.
	intros Square_B_C_E_D.
	intros OppositeSide_D_C_B_A.

	assert (eq D D) as eq_D_D by (reflexivity).
	assert (eq B B) as eq_B_B by (reflexivity).
	pose proof (by_def_Col_from_eq_A_C B C B eq_B_B) as Col_B_C_B.
	pose proof (by_def_Col_from_eq_A_B D D E eq_D_D) as Col_D_D_E.
	
	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_A_B_C) as nCol_A_B_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).
	
	pose proof (lemma_squareparallelogram _ _ _ _ Square_B_C_E_D) as Parallelogram_B_C_E_D.

	pose proof (proposition_34 _ _ _ _ Parallelogram_B_C_E_D) as (_ & Cong_B_C_D_E & _ & _ & _).

	assert (Parallelogram_B_C_E_D_2 := Parallelogram_B_C_E_D).
	destruct Parallelogram_B_C_E_D_2 as (Par_B_C_E_D & Par_B_D_C_E).
	
	pose proof (by_prop_Par_flip _ _ _ _ Par_B_C_E_D) as (Par_C_B_E_D & Par_B_C_D_E & Par_C_B_D_E).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_B_C_E_D) as Par_E_D_B_C.
	pose proof (by_prop_Par_flip _ _ _ _ Par_E_D_B_C) as (Par_D_E_B_C & Par_E_D_C_B & Par_D_E_C_B).
	pose proof (by_prop_Par_NC _ _ _ _ Par_B_C_E_D) as (nCol_B_C_E & nCol_B_E_D & nCol_C_E_D & nCol_B_C_D).

	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_B_C_D) as n_Col_B_C_D.
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_B_C_E) as n_Col_B_C_E.
	
	pose proof (by_prop_Par_flip _ _ _ _ Par_B_D_C_E) as (Par_D_B_C_E & Par_B_D_E_C & Par_D_B_E_C).

	assert (Par_B_C_E_D_2 := Par_B_C_E_D).
	destruct Par_B_C_E_D_2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & n_Meet_B_C_E_D & _ & _).

	assert (Square_B_C_E_D_2 := Square_B_C_E_D).
	destruct Square_B_C_E_D_2 as (
		Cong_B_C_E_D & _ & _ & RightTriangle_D_B_C & _ & RightTriangle_C_E_D & RightTriangle_E_D_B
	).

	pose proof (axiom_nocollapse _ _ _ _ neq_B_C Cong_B_C_E_D) as neq_E_D.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_C_E_D) as RightTriangle_D_E_C.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_B_A_C) as RightTriangle_C_A_B.

	assert (OppositeSide_D_C_B_A_2 := OppositeSide_D_C_B_A).
	destruct OppositeSide_D_C_B_A_2 as (N & BetS_D_N_A & Col_C_B_N &_ ).
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_N_A) as BetS_A_N_D.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_D_N_A) as (neq_N_A & neq_D_N & neq_D_A).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_N_D) as (neq_N_D & neq_A_N & neq_A_D).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_D_N_A) as Col_D_N_A.
	pose proof (by_prop_Col_order _ _ _ Col_D_N_A) as (Col_N_D_A & Col_N_A_D & Col_A_D_N & Col_D_A_N & Col_A_N_D).
	
	pose proof (by_prop_Col_order _ _ _ Col_C_B_N) as (Col_B_C_N & Col_B_N_C & Col_N_C_B & Col_C_N_B & Col_N_B_C).

	pose proof (by_def_OnRay_from_BetS_A_B_E D N A BetS_D_N_A neq_D_N) as OnRay_D_N_A.

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_D_N_A Col_B_C_N nCol_B_C_D) as OppositeSide_D_B_C_A.

	assert (~ eq A E) as n_eq_A_E.
	{
		intro eq_A_E.

		assert (BetS D N E) as BetS_D_N_E by (rewrite <- eq_A_E; exact BetS_D_N_A).
		pose proof (by_def_Col_from_BetS_A_B_C D N E BetS_D_N_E) as Col_D_N_E.
		pose proof (by_prop_Col_order _ _ _ Col_D_N_E) as (_ & _ & Col_E_D_N & _ & _).
		pose proof (by_def_Meet _ _ _ _ _ neq_B_C neq_E_D Col_B_C_N Col_E_D_N) as Meet_B_C_E_D.

		contradict Meet_B_C_E_D.
		exact n_Meet_B_C_E_D.
	}
	assert (neq_A_E := n_eq_A_E).


	assert (~ Col D E A) as n_Col_D_E_A.
	{
		intro Col_D_E_A.

		pose proof (by_prop_Col_order _ _ _ Col_D_E_A) as (_ & _ & _ & Col_D_A_E & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_D_A_E Col_D_A_N neq_D_A) as Col_A_E_N.
		pose proof (by_prop_Col_order _ _ _ Col_A_E_N) as (_ & _ & Col_N_A_E & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_N_A_E Col_N_A_D neq_N_A) as Col_A_E_D.
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_E_D Col_A_E_N neq_A_E) as Col_E_D_N.
		pose proof (by_def_Meet _ _ _ _ _ neq_B_C neq_E_D Col_B_C_N Col_E_D_N) as Meet_B_C_E_D.

		contradict Meet_B_C_E_D.
		exact n_Meet_B_C_E_D.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_D_E_A) as nCol_D_E_A.

	pose proof (proposition_12 _ _ _ nCol_D_E_A) as (L & Perp_at_A_L_D_E_L).

	destruct Perp_at_A_L_D_E_L as (p & _ & Col_D_E_L & Col_D_E_p & RightTriangle_p_L_A).

	pose proof (by_prop_Col_order _ _ _ Col_D_E_L) as (Col_E_D_L & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_E_D_L) as (_ & Col_D_L_E & _ & _ & _).

	pose proof (by_prop_Col_order _ _ _ Col_D_E_p) as (_ & _ & Col_p_D_E & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_D_E_p) as (Col_E_D_p & _ & _ & _ & _).

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_p_L_A) as RightTriangle_A_L_p.

	pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_E_D_p Col_E_D_L neq_E_D) as Col_D_p_L.
	pose proof (by_prop_Col_order _ _ _ Col_D_p_L) as (_ & Col_p_L_D & _ & _ & _).

	assert (~ eq B N) as n_eq_B_N.
	{
		intro eq_B_N.

		assert (BetS D B A) as BetS_D_B_A by (rewrite eq_B_N; exact BetS_D_N_A).
		pose proof (by_def_Col_from_BetS_A_B_C D B A BetS_D_B_A) as Col_D_B_A.
		pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_D_B_C Col_D_B_A neq_A_B) as RightTriangle_A_B_C.
		pose proof (by_prop_RightTriangle_CBA_n_ACB _ _ _ RightTriangle_A_B_C) as n_RightTriangle_C_A_B.

		contradict RightTriangle_C_A_B.
		exact n_RightTriangle_C_A_B.
	}
	assert (neq_B_N := n_eq_B_N).

	pose proof (by_prop_neq_symmetric _ _ neq_B_N) as neq_N_B.

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_D_E_C_B Col_C_B_N neq_N_B) as Par_D_E_N_B.
	pose proof (by_prop_Par_flip _ _ _ _ Par_D_E_N_B) as (_ & Par_D_E_B_N & _).
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_D_E_B_N) as TarskiPar_D_E_B_N.
	assert (TarskiPar_D_E_B_N_2 := TarskiPar_D_E_B_N).
	destruct TarskiPar_D_E_B_N_2 as (_ & _ & _ & SameSide_B_N_D_E).

	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_B_N_D_E Col_D_D_E OnRay_D_N_A) as SameSide_B_A_D_E.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_B_A_D_E) as SameSide_B_A_E_D.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_B_A_E_D) as (SameSide_A_B_E_D & _ & _).

	assert (~ eq D L) as n_eq_D_L.
	{
		intro eq_D_L.

		assert (RightTriangle A D p) as RightTriangle_A_D_p by (rewrite eq_D_L; exact RightTriangle_A_L_p).
		pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_A_D_p) as RightTriangle_p_D_A.
		pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_p_D_A Col_p_D_E neq_E_D) as RightTriangle_E_D_A.
		pose proof (lemma_erectedperpendicularunique _ _ _ _ RightTriangle_E_D_A RightTriangle_E_D_B SameSide_A_B_E_D) as OnRay_D_A_B.
		pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_D_A_B) as Col_D_A_B.
		pose proof (by_prop_Col_order _ _ _ Col_D_A_B) as (Col_A_D_B & _ & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_D_B Col_A_D_N neq_A_D) as Col_D_B_N.
		pose proof (by_prop_Col_order _ _ _ Col_D_B_N) as (_ & _ & _ & _ & Col_N_B_D).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_N_B_C Col_N_B_D neq_N_B) as Col_B_C_D.

		contradict Col_B_C_D.
		exact n_Col_B_C_D.
	}
	assert (neq_D_L := n_eq_D_L).

	pose proof (by_prop_neq_symmetric _ _ neq_D_L) as neq_L_D.

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_E_D_B Col_E_D_L neq_L_D) as RightTriangle_L_D_B.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_L_D_B) as RightTriangle_B_D_L.

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_p_L_A Col_p_L_D neq_D_L) as RightTriangle_D_L_A.

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_B_C_E_D Col_E_D_L neq_L_D) as Par_B_C_L_D.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_B_C_L_D) as Par_L_D_B_C.
	pose proof (by_prop_Par_flip _ _ _ _ Par_L_D_B_C) as (_ & Par_L_D_C_B & _).

	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_B_C_L_D) as TarskiPar_B_C_L_D.
	assert (TarskiPar_B_C_L_D_2 := TarskiPar_B_C_L_D).
	destruct TarskiPar_B_C_L_D_2 as (_ & _ & _ & SameSide_L_D_B_C).

	pose proof (lemma_planeseparation _ _ _ _ _ SameSide_L_D_B_C OppositeSide_D_B_C_A) as OppositeSide_L_B_C_A.

	destruct OppositeSide_L_B_C_A as (M & BetS_L_M_A & Col_B_C_M &_ ).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_L_M_A) as BetS_A_M_L.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_L_M_A) as (_ & neq_L_M & _).
	
	pose proof (by_def_OnRay_from_BetS_A_B_E L M A BetS_L_M_A neq_L_M) as OnRay_L_M_A.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_L_M_A) as OnRay_L_A_M.

	pose proof (by_prop_Col_order _ _ _ Col_B_C_M) as (Col_C_B_M & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_C_B_M) as (_ & _ & Col_M_C_B & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_C_B_M) as (_ & Col_B_M_C & _ & _ & _).
	
	pose proof (by_prop_RightTriangle_leg_change _ _ _ _ RightTriangle_D_L_A OnRay_L_A_M) as RightTriangle_D_L_M.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_D_L_M) as RightTriangle_M_L_D.

	assert (~ eq B M) as n_eq_B_M.
	{
		intro eq_B_M.

		assert (RightTriangle D L B) as RightTriangle_D_L_B by (rewrite eq_B_M; exact RightTriangle_D_L_M).
		pose proof (by_prop_RightTriangle_CBA_n_ACB _ _ _ RightTriangle_D_L_B) as n_RightTriangle_B_D_L.

		contradict RightTriangle_B_D_L.
		exact n_RightTriangle_B_D_L.
	}
	assert (neq_B_M := n_eq_B_M).

	pose proof (by_prop_neq_symmetric _ _ neq_B_M) as neq_M_B.

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_L_D_C_B Col_C_B_M neq_M_B) as Par_L_D_M_B.
	pose proof (by_prop_Par_flip _ _ _ _ Par_L_D_M_B) as (Par_D_L_M_B & Par_L_D_B_M & Par_D_L_B_M).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_L_D_M_B) as Par_M_B_L_D.
	pose proof (by_prop_Par_flip _ _ _ _ Par_M_B_L_D) as (Par_B_M_L_D & Par_M_B_D_L & Par_B_M_D_L).

	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_D_L_B_M) as TarskiPar_D_L_B_M.
	assert (TarskiPar_D_L_B_M_2 := TarskiPar_D_L_B_M).
	destruct TarskiPar_D_L_B_M_2 as (_ & _ & _ & SameSide_B_M_D_L).

	pose proof (lemma_twoperpsparallel _ _ _ _ RightTriangle_B_D_L RightTriangle_D_L_M SameSide_B_M_D_L) as Par_B_D_L_M.

	pose proof (by_prop_Par_flip _ _ _ _ Par_B_D_L_M) as (_ & Par_B_D_M_L & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_B_D_M_L) as Par_M_L_B_D.

	pose proof (by_def_Parallelogram _ _ _ _ Par_B_M_L_D Par_B_D_M_L) as Parallelogram_B_M_L_D.

	pose proof (proposition_34 _ _ _ _ Parallelogram_B_M_L_D) as (_ & Cong_B_M_D_L & _ & _ & _).

	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_M_L_B_D) as TarskiPar_M_L_B_D.
	assert (TarskiPar_M_L_B_D_2 := TarskiPar_M_L_B_D).
	destruct TarskiPar_M_L_B_D_2 as (_ & _ & _ & SameSide_B_D_M_L).

	pose proof (proposition_29C _ _ _ _ _ Par_M_B_L_D SameSide_B_D_M_L BetS_A_M_L) as (CongA_A_M_B_M_L_D & _).
	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_M_L_D CongA_A_M_B_M_L_D) as RightTriangle_A_M_B.

	pose proof (lemma_altitudeofrighttriangle _ _ _ _ _ RightTriangle_B_A_C RightTriangle_A_M_B Col_B_C_B Col_B_C_M) as BetS_B_M_C.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_C) as BetS_C_M_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_M_C) as (neq_M_C & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_M_B) as (_ & neq_C_M & _).


	assert (~ eq L E) as n_eq_L_E.
	{
		intro eq_L_E.

		assert (Par M E B D) as Par_M_E_B_D by (rewrite <- eq_L_E; exact Par_M_L_B_D).
		pose proof (by_prop_Par_symmetric _ _ _ _ Par_M_E_B_D) as Par_B_D_M_E.
		pose proof (by_prop_Par_flip _ _ _ _ Par_B_D_M_E) as (_ & Par_B_D_E_M & _).
		pose proof (lemma_Playfair _ _ _ _ _ Par_B_D_E_C Par_B_D_E_M) as Col_E_C_M.
		pose proof (by_prop_Col_order _ _ _ Col_E_C_M) as (_ & _ & _ & _ & Col_M_C_E).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_M_C_E Col_M_C_B neq_M_C) as Col_C_E_B.
		pose proof (by_prop_Col_order _ _ _ Col_C_E_B) as (_ & _ & Col_B_C_E & _ & _).

		contradict Col_B_C_E.
		exact n_Col_B_C_E.
	}
	assert (neq_L_E := n_eq_L_E).

	pose proof (by_prop_neq_symmetric _ _ neq_L_E) as neq_E_L.

	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_B_M_D_L Col_D_L_E neq_E_L) as Par_B_M_E_L.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_B_M_E_L) as Par_E_L_B_M.
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_E_L_B_M Col_B_M_C neq_C_M) as Par_E_L_C_M.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_E_L_C_M) as Par_C_M_E_L.
	pose proof (by_prop_Par_flip _ _ _ _ Par_C_M_E_L) as (Par_M_C_E_L & _ & _).
	pose proof (by_prop_Par_flip _ _ _ _ Par_M_C_E_L) as (_ & Par_M_C_L_E & _).
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_M_C_L_E) as Par_L_E_M_C.

	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_L_E_M_C) as TarskiPar_L_E_M_C.
	assert (TarskiPar_L_E_M_C_2 := TarskiPar_L_E_M_C).
	destruct TarskiPar_L_E_M_C_2 as (_ & _ & _ & SameSide_M_C_L_E).

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_D_L_M Col_D_L_E neq_E_L) as RightTriangle_E_L_M.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_E_L_M) as RightTriangle_M_L_E.

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_D_E_C Col_D_E_L neq_L_E) as RightTriangle_L_E_C.

	pose proof (lemma_twoperpsparallel _ _ _ _ RightTriangle_M_L_E RightTriangle_L_E_C SameSide_M_C_L_E) as Par_M_L_E_C.
	pose proof (by_prop_Par_flip _ _ _ _ Par_M_L_E_C) as (_ & Par_M_L_C_E & _).

	pose proof (by_def_Parallelogram _ _ _ _ Par_M_C_E_L Par_M_L_C_E) as Parallelogram_M_C_E_L.

	pose proof (proposition_34 _ _ _ _ Parallelogram_M_C_E_L) as (_ & Cong_M_C_L_E & _ & _ & _).

	pose proof (lemma_betweennesspreserved _ _ _ _ _ _ Cong_B_M_D_L Cong_B_C_D_E Cong_M_C_L_E BetS_B_M_C) as BetS_D_L_E.

	exists M, L.
	split.
	exact Parallelogram_B_M_L_D.
	split.
	exact BetS_B_M_C.
	split.
	exact Parallelogram_M_C_E_L.
	split.
	exact BetS_D_L_E.
	split.
	exact BetS_L_M_A.
	exact RightTriangle_D_L_A.
Qed.

End Euclid.
