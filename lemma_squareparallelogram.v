Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Midpoint.
Require Import ProofCheckingEuclid.by_def_OnRay.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_Square.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_OnRay_assert.
Require Import ProofCheckingEuclid.by_prop_OppositeSide_flip.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_collinear.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_Euclid4.
Require Import ProofCheckingEuclid.lemma_betweennesspreserved.
Require Import ProofCheckingEuclid.lemma_diagonalsbisect.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_righttogether.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_46.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

(* Can't use lemma_twoperpsparallel since SameSide needs to be proven first. *)
Lemma lemma_squareparallelogram :
	forall A B C D,
	Square A B C D ->
	Parallelogram A B C D.
Proof.
	intros A B C D.
	intros Square_A_B_C_D.

	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C D A A eq_A_A) as Col_D_A_A.

	pose proof (cn_congruencereflexive D A) as Cong_D_A_D_A.

	destruct Square_A_B_C_D as (
		Cong_A_B_C_D & Cong_A_B_B_C & Cong_A_B_D_A & RightTriangle_D_A_B & RightTriangle_A_B_C & RightTriangle_B_C_D & RightTriangle_C_D_A
	).

	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_D_A_B) as nCol_D_A_B.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_D_A_B) as (neq_D_A & _ & _ & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_D_A_B) as (_ & neq_A_B & _ & _ & _ & _).

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_C_D_A) as RightTriangle_A_D_C.
	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_C_D_A) as nCol_C_D_A.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_C_D_A) as (_ & _ & _ & neq_D_C & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B D C neq_D_C) as OnRay_D_C_C.

	pose proof (lemma_extension D A D A neq_D_A neq_D_A) as (R & BetS_D_A_R & _).
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_A_R) as BetS_R_A_D.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_D_A_R) as (neq_A_R & _ & neq_D_R).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_R_A_D) as (neq_A_D & neq_R_A & neq_R_D).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_D_A_R) as Col_D_A_R.
	pose proof (by_prop_Col_order _ _ _ Col_D_A_R) as (Col_A_D_R & Col_A_R_D & Col_R_D_A & Col_D_R_A & Col_R_A_D).

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_D_A_B Col_D_A_R Col_D_A_A neq_R_A) as nCol_R_A_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_R_A_B) as (_ & nCol_A_B_R & _ & _ & _).

	pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_D_A_B Col_D_A_R neq_R_A) as RightTriangle_R_A_B.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_R_A_B) as RightTriangle_B_A_R.

	pose proof (by_def_OnRay_from_neq_A_B A D neq_A_D) as OnRay_A_D_D.

	pose proof (proposition_46 _ _ _ neq_A_B nCol_A_B_R) as (c & E & Square_A_B_c_E & OppositeSide_E_A_B_R & Parallelogram_A_B_c_E).

	assert (Square_A_B_c_E_2 := Square_A_B_c_E).
	destruct Square_A_B_c_E_2 as (
		Cong_A_B_c_E & Cong_A_B_B_c & Cong_A_B_E_A & RightTriangle_E_A_B & RightTriangle_A_B_c & RightTriangle_B_c_E & RightTriangle_c_E_A
	).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_A_B_B_c) as Cong_B_c_A_B.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_B_c_A_B Cong_A_B_B_C) as Cong_B_c_B_C.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_B_c_B_C) as (Cong_c_B_C_B & _ & _).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_A_B_E_A) as Cong_E_A_A_B.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_E_A_A_B Cong_A_B_D_A) as Cong_E_A_D_A.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_E_A_D_A) as (Cong_A_E_A_D & _ & _).

	pose proof (by_prop_OppositeSide_flip _ _ _ _ OppositeSide_E_A_B_R) as OppositeSide_E_B_A_R.

	pose proof (lemma_righttogether _ _ _ _ RightTriangle_E_A_B RightTriangle_B_A_R OppositeSide_E_B_A_R) as (_ & BetS_E_A_R).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_A_R) as BetS_R_A_E.
	pose proof (by_def_OnRay _ _ _ _ BetS_R_A_D BetS_R_A_E) as OnRay_A_D_E.
	pose proof (lemma_layoffunique _ _ _ _ OnRay_A_D_E OnRay_A_D_D Cong_A_E_A_D) as eq_E_D.

	assert (Parallelogram A B c D) as Parallelogram_A_B_c_D by (rewrite <- eq_E_D; exact Parallelogram_A_B_c_E).

	assert (Square A B c D) as Square_A_B_c_D by (rewrite <- eq_E_D; exact Square_A_B_c_E).

	assert (Square_A_B_c_D_2 := Square_A_B_c_D).
	destruct Square_A_B_c_D_2 as (Cong_A_B_c_D & _ & _ & _ & _ & RightTriangle_B_c_D & RightTriangle_c_D_A).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_A_B_c_D) as Cong_c_D_A_B.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_c_D_A_B Cong_A_B_C_D) as Cong_c_D_C_D.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_c_D_C_D) as (Cong_D_c_D_C & _ & _).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_D_c_D_C) as Cong_D_C_D_c.

	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_B_c_D RightTriangle_B_C_D) as CongA_B_c_D_B_C_D.

	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_c_D_A) as RightTriangle_A_D_c.
	pose proof (lemma_Euclid4 _ _ _ _ _ _ RightTriangle_A_D_C RightTriangle_A_D_c) as CongA_A_D_C_A_D_c.

	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_c_D_A) as nCol_c_D_A.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_c_D_A) as (_ & _ & _ & neq_D_c & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B D c neq_D_c) as OnRay_D_c_c.

	pose proof (proposition_04 _ _ _ _ _ _ Cong_c_B_C_B Cong_c_D_C_D CongA_B_c_D_B_C_D) as (
		_ & _ & CongA_c_D_B_C_D_B
	).
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_c_D_B_C_D_B) as CongA_C_D_B_c_D_B.

	pose proof (lemma_diagonalsbisect _ _ _ _ Parallelogram_A_B_c_D) as (m & Midpoint_A_m_c & Midpoint_B_m_D).

	pose proof (cn_congruencereflexive A m) as Cong_A_m_A_m.
	pose proof (cn_congruencereflexive D m) as Cong_D_m_D_m.

	destruct Midpoint_A_m_c as (BetS_A_m_c & _).
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_m_c) as BetS_c_m_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_m_c) as (neq_m_c & neq_A_m & neq_A_c).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_c_m_A) as (neq_m_A & neq_c_m & neq_c_A).

	pose proof (by_def_OnRay_from_BetS_A_B_E A m c BetS_A_m_c neq_A_m) as OnRay_A_m_c.

	destruct Midpoint_B_m_D as (BetS_B_m_D & _).
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_m_D) as BetS_D_m_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_m_D) as (neq_m_D & neq_B_m & neq_B_D).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_D_m_B) as (neq_m_B & neq_D_m & neq_D_B).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_m_D) as Col_B_m_D.
	pose proof (by_prop_Col_order _ _ _ Col_B_m_D) as (Col_m_B_D & Col_m_D_B & Col_D_B_m & Col_B_D_m & Col_D_m_B).

	pose proof (by_def_OnRay_from_BetS_A_E_B D B m BetS_D_m_B neq_D_B) as OnRay_D_B_m.


	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_c_D_B_C_D_B OnRay_D_C_C OnRay_D_B_m) as CongA_c_D_B_C_D_m.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_c_D_B_C_D_m) as CongA_C_D_m_c_D_B.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_C_D_m_c_D_B OnRay_D_c_c OnRay_D_B_m) as CongA_C_D_m_c_D_m.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_C_D_m_c_D_m) as CongA_c_D_m_C_D_m.

	pose proof (proposition_04 _ _ _ _ _ _ Cong_D_c_D_C Cong_D_m_D_m CongA_c_D_m_C_D_m) as (Cong_c_m_C_m & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_c_m_C_m) as (Cong_m_c_m_C & _ & _).

	pose proof (proposition_04 _ _ _ _ _ _ Cong_D_A_D_A Cong_D_C_D_c CongA_A_D_C_A_D_c) as (Cong_A_C_A_c & _ & _).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_A_C_A_c) as Cong_A_c_A_C.

	pose proof (lemma_betweennesspreserved _ _ _ _ _ _ Cong_A_m_A_m Cong_A_c_A_C Cong_m_c_m_C BetS_A_m_c) as BetS_A_m_C.

	pose proof (by_def_OnRay_from_BetS_A_B_E A m C BetS_A_m_C neq_A_m) as OnRay_A_m_C.

	pose proof (lemma_layoffunique _ _ _ _ OnRay_A_m_c OnRay_A_m_C Cong_A_c_A_C) as eq_c_C.

	assert (Parallelogram A B C D) as Parallelogram_A_B_C_D by (rewrite <- eq_c_C; exact Parallelogram_A_B_c_D).

	exact Parallelogram_A_B_C_D.
Qed.

End Euclid.
