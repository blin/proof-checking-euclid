Require Import ProofCheckingEuclid.by_def_Cross.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_def_Rectangle.
Require Import ProofCheckingEuclid.by_def_SumTwoRT.
Require Import ProofCheckingEuclid.by_def_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_equaltoright.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_supplement.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_diagonalsmeet.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.proposition_29C.
Require Import ProofCheckingEuclid.proposition_34.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_PGrectangle :
	forall A B C D,
	Parallelogram A C D B ->
	RightTriangle B A C ->
	Rectangle A C D B.
Proof.
	intros A B C D.
	intros Parallelogram_A_C_D_B.
	intros RightTriangle_B_A_C.

	pose proof (proposition_34 _ _ _ _ Parallelogram_A_C_D_B) as (
		Cong_A_B_C_D & Cong_A_C_B_D & CongA_C_A_B_B_D_C & CongA_A_B_D_D_C_A & CongTriangles_C_A_B_B_D_C
	).
	assert (Parallelogram_A_C_D_B_2 := Parallelogram_A_C_D_B).
	destruct Parallelogram_A_C_D_B_2 as (Par_A_C_D_B & Par_A_B_C_D).
	pose proof (by_prop_Par_NC _ _ _ _ Par_A_C_D_B) as (_ & _ & _ & nCol_A_C_B).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_C_B) as (_ & _ & _ & nCol_A_B_C & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_C_B) as (nCol_C_A_B & _ & _ & _ & _).
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_C_A_B) as CongA_C_A_B_B_A_C.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_B_A_C) as RightTriangle_C_A_B.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & _ & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_C_A_B_B_A_C) as CongA_B_A_C_C_A_B.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_B_A_C_C_A_B CongA_C_A_B_B_D_C) as CongA_B_A_C_B_D_C.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_B_A_C_B_D_C) as CongA_B_D_C_B_A_C.
	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_B_A_C CongA_B_D_C_B_A_C) as RightTriangle_B_D_C.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_B_D_C) as RightTriangle_C_D_B.
	pose proof (by_prop_Par_flip _ _ _ _ Par_A_C_D_B) as (_ & Par_A_C_B_D & _).
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_A_B_C_D) as TarskiPar_A_B_C_D.

	assert (TarskiPar_A_B_C_D_2 := TarskiPar_A_B_C_D).
	destruct TarskiPar_A_B_C_D_2 as (_ & neq_C_D & n_Meet_A_B_C_D & SameSide_C_D_A_B).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_C_A_B) as (neq_C_A & _ & _ & _ & _ & _).
	pose proof (lemma_extension B A A B neq_B_A neq_A_B) as (E & BetS_B_A_E & Cong_A_E_A_B).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_E) as BetS_E_A_B.
	pose proof (proposition_29C _ _ _ _ _ Par_A_C_B_D SameSide_C_D_A_B BetS_E_A_B) as (_ & SumTwoRT_C_A_B_A_B_D).

	destruct SumTwoRT_C_A_B_A_B_D as (p & q & r & s & t & Supp_p_q_r_s_t & CongA_C_A_B_p_q_r & CongA_A_B_D_s_q_t).
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_C_A_B_p_q_r) as CongA_p_q_r_C_A_B.
	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_C_A_B CongA_p_q_r_C_A_B) as RightTriangle_p_q_r.
	pose proof (by_prop_RightTriangle_supplement _ _ _ _ _ Supp_p_q_r_s_t RightTriangle_p_q_r) as (_ & RightTriangle_s_q_t).
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_A_B_D_s_q_t) as CongA_s_q_t_A_B_D.
	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_s_q_t CongA_A_B_D_s_q_t) as RightTriangle_A_B_D.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_A_B_D) as RightTriangle_D_B_A.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_A_B_D_D_C_A) as CongA_D_C_A_A_B_D.
	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_A_B_D CongA_D_C_A_A_B_D) as RightTriangle_D_C_A.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_D_C_A) as RightTriangle_A_C_D.
	pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_A_C_D_B) as (M & BetS_A_M_D & BetS_C_M_B).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_M_D) as (_ & _ & neq_A_D).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_M_B) as (_ & _ & neq_C_B).
	pose proof (by_def_Cross _ _ _ _ _ BetS_A_M_D BetS_C_M_B) as Cross_A_D_C_B.
	pose proof (by_def_Rectangle _ _ _ _ RightTriangle_B_A_C RightTriangle_A_C_D RightTriangle_C_D_B RightTriangle_D_B_A Cross_A_D_C_B) as Rectangle_A_C_D_B.

	exact Rectangle_A_C_D_B.
Qed.

End Euclid.
