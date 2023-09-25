Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B.
Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Cross.
Require Import ProofCheckingEuclid.by_def_Midpoint.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_flip.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_crossimpliesopposite.
Require Import ProofCheckingEuclid.lemma_diagonalsmeet.
Require Import ProofCheckingEuclid.proposition_26A.
Require Import ProofCheckingEuclid.proposition_29B.
Require Import ProofCheckingEuclid.proposition_34.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_diagonalsbisect :
	forall A B C D,
	Parallelogram A B C D ->
	exists X, Midpoint A X C /\ Midpoint B X D.
Proof.
	intros A B C D.
	intros Parallelogram_A_B_C_D.

	assert (eq D D) as eq_D_D by (reflexivity).
	pose proof (by_def_Col_from_eq_B_C B D D eq_D_D) as Col_B_D_D.

	pose proof (proposition_34 _ _ _ _ Parallelogram_A_B_C_D) as (_ & Cong_AB_DC & _ & _ & _).

	assert (Parallelogram_A_B_C_D_2 := Parallelogram_A_B_C_D).
	destruct Parallelogram_A_B_C_D_2 as (Par_AB_CD & Par_AD_BC).

	pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_A_B_C_D) as (M & BetS_A_M_C & BetS_B_M_D).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_M_C) as BetS_C_M_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_M_C) as (neq_M_C & neq_A_M & neq_A_C).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_M_A) as (neq_M_A & neq_C_M & neq_C_A).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_M_C) as Col_A_M_C.
	pose proof (by_prop_Col_order _ _ _ Col_A_M_C) as (Col_M_A_C & Col_M_C_A & Col_C_A_M & Col_A_C_M & Col_C_M_A).

	pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_C_M_A neq_C_A) as OnRay_CA_M.
	pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_A_M_C neq_A_C) as OnRay_AC_M.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_M_D) as BetS_D_M_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_M_D) as (neq_M_D & neq_B_M & neq_B_D).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_D_M_B) as (neq_M_B & neq_D_M & neq_D_B).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_M_D) as Col_B_M_D.
	pose proof (by_prop_Col_order _ _ _ Col_B_M_D) as (Col_M_B_D & Col_M_D_B & Col_D_B_M & Col_B_D_M & Col_D_M_B).


	pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_B_M_D neq_B_D) as OnRay_BD_M.
	pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_D_M_B neq_D_B) as OnRay_DB_M.

	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_CD) as (_ & Par_AB_DC & _).
	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_DC) as (Par_BA_DC & _ & _).
	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_CD) as (Par_BA_CD & _ & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_BA_DC) as (nCol_B_A_D & _ & _ & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_DC) as (nCol_A_B_D & _ & _ & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (nCol_A_B_C & _ & _ & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (_ & nCol_A_C_D & _ & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_BA_DC) as (_ & nCol_B_D_C & _ & _).

	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & _ & _ & _ & _).
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_C_D) as n_Col_A_C_D.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_D_C Col_B_D_M Col_B_D_D neq_M_D) as nCol_M_D_C.

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_D) as (neq_A_B & _ & _ & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_A_C) as (neq_B_A & _ & _ & _ & _ & _).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_B_D_C) as (_ & neq_D_C & _ & _ & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_D_C) as OnRay_DC_C.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_A_B) as OnRay_AB_B.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_A) as OnRay_BA_A.

	pose proof (by_prop_CongA_reflexive _ _ _ nCol_A_B_D) as CongA_ABD_ABD.
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_A_C_D) as CongA_ACD_ACD.
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_B_A_C) as CongA_BAC_BAC.
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_B_D_C) as CongA_BDC_BDC.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_M_D_C) as CongA_MDC_CDM.

	pose proof (by_def_Cross _ _ _ _ _ BetS_A_M_C BetS_B_M_D) as Cross_AC_BD.
	pose proof (by_def_Cross _ _ _ _ _ BetS_B_M_D BetS_A_M_C) as Cross_BD_AC.
	pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_AC_BD nCol_A_B_D) as (OppositeSide_A_BD_C & _ & _ & _).
	pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_BD_AC nCol_B_A_C) as (OppositeSide_B_AC_D & _ & _ & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_DC) as (_ & _ & Cong_AB_CD).

	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_C) as n_Col_A_B_C.

	assert (~ Col M A B) as n_Col_M_A_B.
	{
		intro Col_M_A_B.

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_M_A_B Col_M_A_C neq_M_A) as Col_A_B_C.

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_M_A_B) as nCol_M_A_B.
	pose proof (by_def_Triangle _ _ _ nCol_M_A_B) as Triangle_MAB.

	assert (~ Col M C D) as n_Col_M_C_D.
	{
		intro Col_M_C_D.

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_M_C_D Col_M_C_A neq_M_C) as Col_C_D_A.
		pose proof (by_prop_Col_order _ _ _ Col_C_D_A) as (_ & _ & Col_A_C_D & _ & _).

		contradict Col_A_C_D.
		exact n_Col_A_C_D.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_M_C_D) as nCol_M_C_D.
	pose proof (by_def_Triangle _ _ _ nCol_M_C_D) as Triangle_MCD.

	pose proof (by_prop_nCol_distinct _ _ _ nCol_M_C_D) as (_ & neq_C_D & _ & _ & _ & _).
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_D) as OnRay_CD_D.

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_M_C_D) as CongA_MCD_DCM.

	pose proof (proposition_29B _ _ _ _ Par_BA_CD OppositeSide_B_AC_D) as CongA_BAC_ACD.

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_BAC_BAC OnRay_AB_B OnRay_AC_M) as CongA_BAC_BAM.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_BAC_BAM) as CongA_BAM_BAC.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_BAM_BAC CongA_BAC_ACD) as CongA_BAM_ACD.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_ACD_ACD OnRay_CA_M OnRay_CD_D) as CongA_ACD_MCD.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_BAM_ACD CongA_ACD_MCD) as CongA_BAM_MCD.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_BAM_MCD CongA_MCD_DCM) as CongA_BAM_DCM.

	pose proof (proposition_29B _ _ _ _ Par_AB_DC OppositeSide_A_BD_C) as CongA_ABD_BDC.

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_ABD_ABD OnRay_BA_A OnRay_BD_M) as CongA_ABD_ABM.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ABD_ABM) as CongA_ABM_ABD.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABM_ABD CongA_ABD_BDC) as CongA_ABM_BDC.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_BDC_BDC OnRay_DB_M OnRay_DC_C) as CongA_BDC_MDC.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABM_BDC CongA_BDC_MDC) as CongA_ABM_MDC.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABM_MDC CongA_MDC_CDM) as CongA_ABM_CDM.
	pose proof (by_prop_CongA_flip _ _ _ _ _ _ CongA_BAM_DCM) as CongA_MAB_MCD.

	pose proof (proposition_26A _ _ _ _ _ _ Triangle_MAB Triangle_MCD CongA_MAB_MCD CongA_ABM_CDM Cong_AB_CD) as (Cong_MA_MC & Cong_MB_MD & CongA_AMB_CMD).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_MA_MC) as (_ & Cong_AM_MC & _).
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_MB_MD) as (_ & Cong_BM_MD & _).

	pose proof (by_def_Midpoint _ _ _ BetS_A_M_C Cong_AM_MC) as Midpoint_A_M_C.
	pose proof (by_def_Midpoint _ _ _ BetS_B_M_D Cong_BM_MD) as Midpoint_B_M_D.

	exists M.
	split.
	exact Midpoint_A_M_C.
	exact Midpoint_B_M_D.
Qed.

End Euclid.
