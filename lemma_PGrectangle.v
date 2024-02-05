Require Import ProofCheckingEuclid.by_def_Cross.
Require Import ProofCheckingEuclid.by_def_Rectangle.
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
	intros RightTriangle_BAC.

	pose proof (proposition_34 _ _ _ _ Parallelogram_A_C_D_B) as (
		Cong_AB_CD & Cong_AC_BD & CongA_CAB_BDC & CongA_ABD_DCA & CongTriangles_CAB_BDC
	).
	assert (Parallelogram_A_C_D_B_2 := Parallelogram_A_C_D_B).
	destruct Parallelogram_A_C_D_B_2 as (Par_AC_DB & Par_AB_CD).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AC_DB) as (_ & _ & _ & nCol_A_C_B).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_C_B) as (_ & _ & _ & nCol_A_B_C & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_C_B) as (nCol_C_A_B & _ & _ & _ & _).
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_C_A_B) as CongA_CAB_BAC.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_BAC) as RightTriangle_CAB.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (neq_A_B & _ & _ & _ & _ & _).
	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_CAB_BAC) as CongA_BAC_CAB.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_BAC_CAB CongA_CAB_BDC) as CongA_BAC_BDC.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_BAC_BDC) as CongA_BDC_BAC.
	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_BAC CongA_BDC_BAC) as RightTriangle_BDC.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_BDC) as RightTriangle_CDB.
	pose proof (by_prop_Par_flip _ _ _ _ Par_AC_DB) as (_ & Par_AC_BD & _).
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_AB_CD) as TarskiPar_AB_CD.

	assert (TarskiPar_AB_CD_2 := TarskiPar_AB_CD).
	destruct TarskiPar_AB_CD_2 as (_ & neq_C_D & n_Meet_A_B_C_D & SameSide_C_D_AB).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_C_A_B) as (neq_C_A & _ & _ & _ & _ & _).
	pose proof (lemma_extension _ _ _ _ neq_B_A neq_A_B) as (E & BetS_B_A_E & Cong_AE_AB).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_E) as BetS_E_A_B.
	pose proof (proposition_29C _ _ _ _ _ Par_AC_BD SameSide_C_D_AB BetS_E_A_B) as (_ & SumTwoRT_CAB_ABD).

	destruct SumTwoRT_CAB_ABD as (p & q & r & s & t & Supp_pqr_sqt & CongA_CAB_pqr & CongA_ABD_sqt).
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_CAB_pqr) as CongA_pqr_CAB.
	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_CAB CongA_pqr_CAB) as RightTriangle_pqr.
	pose proof (by_prop_RightTriangle_supplement _ _ _ _ _ Supp_pqr_sqt RightTriangle_pqr) as (_ & RightTriangle_sqt).
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ABD_sqt) as CongA_sqt_ABD.
	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_sqt CongA_ABD_sqt) as RightTriangle_ABD.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_ABD) as RightTriangle_DBA.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ABD_DCA) as CongA_DCA_ABD.
	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_ABD CongA_DCA_ABD) as RightTriangle_DCA.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_DCA) as RightTriangle_ACD.
	pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_A_C_D_B) as (M & BetS_A_M_D & BetS_C_M_B).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_M_D) as (_ & _ & neq_A_D).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_M_B) as (_ & _ & neq_C_B).
	pose proof (by_def_Cross _ _ _ _ _ BetS_A_M_D BetS_C_M_B) as Cross_AD_CB.
	pose proof (by_def_Rectangle _ _ _ _ RightTriangle_BAC RightTriangle_ACD RightTriangle_CDB RightTriangle_DBA Cross_AD_CB) as Rectangle_A_C_D_B.

	exact Rectangle_A_C_D_B.
Qed.

End Euclid.
